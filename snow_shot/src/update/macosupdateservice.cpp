#include "snow_shot/app/edition.h"
#include "snow_shot/update/updateservice.h"

#include <QCoreApplication>
#include <QCryptographicHash>
#include <QDir>
#include <QEvent>
#include <QFile>
#include <QFileInfo>
#include <QJsonArray>
#include <QJsonDocument>
#include <QJsonObject>
#include <QNetworkAccessManager>
#include <QNetworkProxyFactory>
#include <QNetworkReply>
#include <QPointer>
#include <QProcess>
#include <QRegularExpression>
#include <QSaveFile>
#include <QSet>
#include <QUrlQuery>
#include <QTimer>
#include <QVector>
#include <optional>
#include <algorithm>

namespace snow_shot::update {
namespace {
constexpr qint64 MAXIMUM_RESPONSE_BYTES = 8 * 1024 * 1024;
constexpr qint64 MAXIMUM_PACKAGE_BYTES = 2LL * 1024 * 1024 * 1024;
constexpr qsizetype MAXIMUM_CHECKSUM_BYTES = 1024;

struct Version {
    QStringList core;
    QStringList prerelease;
};

std::optional<Version> parseVersion(const QString& text) {
    static const QRegularExpression pattern(
        QStringLiteral("\\A(0|[1-9][0-9]*)\\.(0|[1-9][0-9]*)\\.(0|[1-9][0-9]*)"
                       "(?:-([0-9A-Za-z-]+(?:\\.[0-9A-Za-z-]+)*))?"
                       "(?:\\+([0-9A-Za-z-]+(?:\\.[0-9A-Za-z-]+)*))?\\z"));
    const auto match = pattern.match(text);
    if (!match.hasMatch())
        return std::nullopt;
    Version version{{match.captured(1), match.captured(2), match.captured(3)}, {}};
    if (!match.captured(4).isEmpty()) {
        version.prerelease = match.captured(4).split(u'.');
        for (const auto& identifier : version.prerelease) {
            if (identifier.size() > 1 && identifier.front() == u'0' &&
                std::all_of(identifier.begin(), identifier.end(),
                            [](QChar c) { return c >= u'0' && c <= u'9'; }))
                return std::nullopt;
        }
    }
    return version;
}

bool numeric(const QString& text) {
    return std::all_of(text.begin(), text.end(), [](QChar c) { return c >= u'0' && c <= u'9'; });
}

int compareIdentifier(const QString& left, const QString& right, bool number) {
    if (number && left.size() != right.size())
        return left.size() < right.size() ? -1 : 1;
    return QString::compare(left, right, Qt::CaseSensitive);
}

int compareVersions(const Version& left, const Version& right) {
    for (qsizetype i = 0; i < 3; ++i) {
        const int order = compareIdentifier(left.core[i], right.core[i], true);
        if (order != 0)
            return order;
    }
    if (left.prerelease.isEmpty() != right.prerelease.isEmpty())
        return left.prerelease.isEmpty() ? 1 : -1;
    for (qsizetype i = 0; i < std::min(left.prerelease.size(), right.prerelease.size()); ++i) {
        const bool leftNumeric = numeric(left.prerelease[i]);
        const bool rightNumeric = numeric(right.prerelease[i]);
        if (leftNumeric != rightNumeric)
            return leftNumeric ? -1 : 1;
        const int order = compareIdentifier(left.prerelease[i], right.prerelease[i], leftNumeric);
        if (order != 0)
            return order;
    }
    return left.prerelease.size() == right.prerelease.size()
               ? 0
               : (left.prerelease.size() < right.prerelease.size() ? -1 : 1);
}

class SystemProxyFactory final : public QNetworkProxyFactory {
    QList<QNetworkProxy> queryProxy(const QNetworkProxyQuery& query) override {
        return systemProxyForQuery(query);
    }
};
} // namespace

struct UpdateService::Impl {
    enum class Source { GitHub, Gitee };
    enum class Stage { Releases, Attachments };

    struct Candidate {
        QString version;
        qint64 releaseId = 0;
        QUrl packageUrl;
        QUrl checksumUrl;
    };

    enum class DownloadStage { None, Package, Checksum };

    struct Channel {
        explicit Channel(QObject* parent) : deadline(parent) {
            deadline.setSingleShot(true);
        }
        QTimer deadline;
        QPointer<QNetworkReply> reply;
        QByteArray bytes;
        QVector<Candidate> candidates;
        qsizetype candidateIndex = 0;
        int page = 1;
        Stage stage = Stage::Releases;
        bool active = false;
    };

    Impl(UpdateService& owner, Options value)
        : q(owner), options(std::move(value)), network(&owner), schedule(&owner), github(&owner),
          gitee(&owner) {
        status.state = UpdateState::Idle;
        if (options.installedVersion.isEmpty())
            options.installedVersion = QStringLiteral(SNOW_SHOT_VERSION);
        schedule.setSingleShot(true);
        QObject::connect(&schedule, &QTimer::timeout, &q, [this] { check(false); });
        QObject::connect(&github.deadline, &QTimer::timeout, &q,
                         [this] { sourceFailure(Source::GitHub); });
        QObject::connect(&gitee.deadline, &QTimer::timeout, &q,
                         [this] { sourceFailure(Source::Gitee); });
        network.setProxy(QNetworkProxy::NoProxy);
    }

    Channel& channel(Source source) {
        return source == Source::GitHub ? github : gitee;
    }
    bool busy() const {
        return github.active || gitee.active || downloadActive;
    }
    bool automaticDownloadEnabled() const {
        return mode == u"download";
    }
    void arm(std::chrono::milliseconds delay) {
        if (started && (mode == u"check" || mode == u"download"))
            schedule.start(delay);
    }
    void stopRequest(Channel& source) {
        source.deadline.stop();
        source.active = false;
        if (source.reply) {
            auto* reply = source.reply.data();
            source.reply.clear();
            reply->disconnect(&q);
            reply->abort();
            reply->deleteLater();
        }
    }
    void reset(Channel& source) {
        stopRequest(source);
        source.bytes = {};
        source.candidates = QVector<Candidate>();
        source.candidateIndex = 0;
        source.page = 1;
        source.stage = Stage::Releases;
    }
    void resetAll() {
        reset(github);
        reset(gitee);
    }
    void finishFailure(const char* error) {
        resetAll();
        status = previous;
        errorSource = previousErrorSource;
        errorContext = QByteArrayLiteral("UpdateService");
        if (manual) {
            errorSource = error;
            status.state = UpdateState::Failed;
            status.error = QCoreApplication::translate("UpdateService", error);
        }
        arm(options.automaticCheckInterval);
        emit q.statusChanged();
        emit q.operationFinished(QStringLiteral("check"), QStringLiteral("failed"));
    }
    void sourceFailure(Source source) {
        reset(channel(source));
        if (!busy())
            finishFailure(QT_TRANSLATE_NOOP("UpdateService",
                                            "Could not check for updates. Please try again."));
    }
    bool validUrl(const QUrl& url) const {
        const bool local =
            options.allowLocalHttp && url.scheme() == u"http" &&
            (url.host() == u"127.0.0.1" || url.host() == u"localhost" || url.host() == u"::1");
        return url.isValid() && !url.host().isEmpty() && (url.scheme() == u"https" || local) &&
               url.userInfo().isEmpty();
    }
    void complete(Source source, const Candidate& candidate) {
        const QString& text = candidate.version;
        const auto version = parseVersion(text);
        if (!version) {
            sourceFailure(source);
            return;
        }
        const bool available =
            compareVersions(*version, *parseVersion(options.installedVersion)) > 0;
        const QString tag = QStringLiteral("v%1_snow-shot").arg(text);
        const QString root =
            source == Source::GitHub
                ? QStringLiteral("https://github.com/mg-chao/snow-apps/releases/tag/")
                : QStringLiteral("https://gitee.com/mg-chao/snow-apps/releases/tag/");
        resetAll();
        checksumUrl = available ? candidate.checksumUrl : QUrl();
        status = {available ? UpdateState::Available : UpdateState::Idle,
                  text,
                  {},
                  0,
                  0,
                  available && !candidate.packageUrl.isEmpty() ? candidate.packageUrl
                                                               : QUrl(root + tag)};
        const bool notify = available && !manual && mode == u"check" && !notified.contains(text);
        if (notify)
            notified.insert(text);
        arm(options.automaticCheckInterval);
        emit q.statusChanged();
        emit q.operationFinished(QStringLiteral("check"), QStringLiteral("success"));
        if (notify)
            emit q.automaticUpdateAvailable(text);
        if (available && automaticDownloadEnabled())
            download(false);
    }
    bool validAssetUrl(Source source, const QUrl& actual, const QString& tag,
                       const QString& assetName) const {
        if (!validUrl(actual))
            return false;
        const QString origin = source == Source::GitHub ? QStringLiteral("https://github.com")
                                                        : QStringLiteral("https://gitee.com");
        const QUrl expected(
            origin +
            QStringLiteral("/mg-chao/snow-apps/releases/download/%1/%2").arg(tag, assetName));
        if (actual == expected)
            return true;
        // Local HTTP endpoints are test-only and must still use the exact API server origin.
        const QUrl api = source == Source::GitHub ? options.githubApiUrl : options.giteeApiUrl;
        return options.allowLocalHttp && api.scheme() == u"http" &&
               (api.host() == u"127.0.0.1" || api.host() == u"localhost" || api.host() == u"::1") &&
               actual.scheme() == api.scheme() && actual.host() == api.host() &&
               actual.port() == api.port() &&
               actual.path() == QStringLiteral("/download/%1/%2").arg(tag, assetName);
    }

    bool validAssets(Source source, const QJsonArray& assets, const QString& text,
                     QUrl* packageUrl = nullptr, QUrl* checksumUrl = nullptr) const {
#if defined(Q_PROCESSOR_ARM_64)
        const QString arch = QStringLiteral("arm64");
#else
        const QString arch = QStringLiteral("x86_64");
#endif
        const QString tag = QStringLiteral("v%1_snow-shot").arg(text);
        const QString name =
            (app::edition::productId() + QStringLiteral("-%1-macos-%2.dmg")).arg(text, arch);
        for (const QString& assetName : {name, name + QStringLiteral(".sha256")}) {
            int matches = 0;
            for (const auto& value : assets) {
                const auto asset = value.toObject();
                if (asset.value(QStringLiteral("name")).toString() != assetName)
                    continue;
                ++matches;
                const QUrl url(asset.value(QStringLiteral("browser_download_url")).toString());
                if (!validAssetUrl(source, url, tag, assetName))
                    return false;
                if (assetName == name && packageUrl)
                    *packageUrl = url;
                if (assetName == name + QStringLiteral(".sha256") && checksumUrl)
                    *checksumUrl = url;
            }
            if (matches != 1)
                return false;
        }
        return true;
    }
    void releasesResponse(Source source) {
        auto& state = channel(source);
        QJsonParseError error;
        const auto document = QJsonDocument::fromJson(state.bytes, &error);
        state.bytes = {};
        if (error.error != QJsonParseError::NoError || !document.isArray() ||
            document.array().size() > 100) {
            sourceFailure(source);
            return;
        }
        for (const auto& value : document.array()) {
            const auto release = value.toObject();
            if (release.value(QStringLiteral("draft")).toBool() ||
                (source == Source::GitHub && !release.value(QStringLiteral("draft")).isBool()))
                continue;
            const QString tag = release.value(QStringLiteral("tag_name")).toString();
            if (!tag.startsWith(u'v') || !tag.endsWith(u"_snow-shot"))
                continue;
            const QString text = tag.mid(1, tag.size() - 11);
            const auto version = parseVersion(text);
            if (!version)
                continue;
            QUrl packageUrl;
            QUrl checksumUrl;
            if (source == Source::GitHub &&
                !validAssets(source, release.value(QStringLiteral("assets")).toArray(), text,
                             &packageUrl, &checksumUrl))
                continue;
            const qint64 releaseId = release.value(QStringLiteral("id")).toVariant().toLongLong();
            if (source == Source::Gitee && releaseId <= 0)
                continue;
            state.candidates.append({text, releaseId, packageUrl, checksumUrl});
        }
        if (document.array().size() == 100) {
            if (state.page == 10) {
                sourceFailure(source);
                return;
            }
            ++state.page;
            request(source);
            return;
        }
        if (state.candidates.isEmpty()) {
            sourceFailure(source);
            return;
        }
        std::sort(state.candidates.begin(), state.candidates.end(),
                  [](const auto& left, const auto& right) {
                      return compareVersions(*parseVersion(left.version),
                                             *parseVersion(right.version)) > 0;
                  });
        state.candidateIndex = 0;
        if (source == Source::GitHub) {
            complete(source, state.candidates.front());
        } else {
            state.stage = Stage::Attachments;
            request(source);
        }
    }
    void attachmentsResponse() {
        QJsonParseError error;
        const auto document = QJsonDocument::fromJson(gitee.bytes, &error);
        gitee.bytes = {};
        if (error.error != QJsonParseError::NoError || !document.isArray() ||
            document.array().size() >= 100) {
            sourceFailure(Source::Gitee);
            return;
        }
        auto& candidate = gitee.candidates[gitee.candidateIndex];
        if (!validAssets(Source::Gitee, document.array(), candidate.version, &candidate.packageUrl,
                         &candidate.checksumUrl)) {
            ++gitee.candidateIndex;
            if (gitee.candidateIndex >= gitee.candidates.size()) {
                sourceFailure(Source::Gitee);
                return;
            }
            request(Source::Gitee);
            return;
        }
        complete(Source::Gitee, candidate);
    }
    void read(Source source) {
        auto& state = channel(source);
        if (!state.reply)
            return;
        const qint64 available = state.reply->bytesAvailable();
        if (available <= 0)
            return;
        state.bytes +=
            state.reply->read(std::min(available, MAXIMUM_RESPONSE_BYTES + 1 - state.bytes.size()));
        if (state.bytes.size() > MAXIMUM_RESPONSE_BYTES)
            sourceFailure(source);
    }
    void request(Source source) {
        auto& state = channel(source);
        // Pagination and attachment fallback still need the compact candidates.
        stopRequest(state);
        QUrl url = source == Source::GitHub ? options.githubApiUrl : options.giteeApiUrl;
        if (state.stage == Stage::Attachments) {
            QString path = url.path();
            if (path.endsWith(u'/'))
                path.chop(1);
            url.setPath(path + u'/' +
                        QString::number(state.candidates[state.candidateIndex].releaseId) +
                        QStringLiteral("/attach_files"));
        }
        QUrlQuery query;
        query.addQueryItem(QStringLiteral("per_page"), QStringLiteral("100"));
        if (state.stage == Stage::Releases)
            query.addQueryItem(QStringLiteral("page"), QString::number(state.page));
        url.setQuery(query);
        if (!validUrl(url)) {
            sourceFailure(source);
            return;
        }
        state.bytes.clear();
        QNetworkRequest request(url);
        request.setAttribute(QNetworkRequest::RedirectPolicyAttribute,
                             QNetworkRequest::SameOriginRedirectPolicy);
        request.setAttribute(QNetworkRequest::CacheLoadControlAttribute,
                             QNetworkRequest::AlwaysNetwork);
        request.setRawHeader("Accept", source == Source::GitHub ? "application/vnd.github+json"
                                                                : "application/json");
        request.setRawHeader("User-Agent", "SnowShot/" + options.installedVersion.toUtf8());
        request.setRawHeader("Cache-Control", "no-cache");
        state.active = true;
        state.reply = network.get(request);
        state.reply->setReadBufferSize(MAXIMUM_RESPONSE_BYTES + 1);
        const QPointer<QNetworkReply> current = state.reply;
        QObject::connect(state.reply, &QNetworkReply::metaDataChanged, &q, [this, source, current] {
            auto& state = channel(source);
            if (state.reply == current && state.reply &&
                state.reply->header(QNetworkRequest::ContentLengthHeader).toLongLong() >
                    MAXIMUM_RESPONSE_BYTES)
                sourceFailure(source);
        });
        QObject::connect(state.reply, &QNetworkReply::readyRead, &q, [this, source, current] {
            if (channel(source).reply == current)
                read(source);
        });
        QObject::connect(state.reply, &QNetworkReply::finished, &q, [this, source, current] {
            auto& state = channel(source);
            if (state.reply != current)
                return;
            read(source);
            if (!state.reply || state.reply != current)
                return;
            if (state.reply->error() != QNetworkReply::NoError ||
                state.reply->attribute(QNetworkRequest::HttpStatusCodeAttribute).toInt() != 200) {
                sourceFailure(source);
                return;
            }
            if (state.stage == Stage::Releases)
                releasesResponse(source);
            else
                attachmentsResponse();
        });
        state.deadline.start(options.requestTimeout);
    }

    QString packageFileName(const QString& version) const {
#if defined(Q_PROCESSOR_ARM_64)
        const QString arch = QStringLiteral("arm64");
#else
        const QString arch = QStringLiteral("x86_64");
#endif
        return (app::edition::productId() + QStringLiteral("-%1-macos-%2.dmg")).arg(version, arch);
    }

    QString updateCacheDirectory() const {
        if (!options.cacheDirectory.isEmpty())
            return options.cacheDirectory;
        return QDir(QCoreApplication::applicationDirPath())
            .filePath(QStringLiteral(".snow-shot-updates"));
    }

    void stopDownload(bool removePartial) {
        downloadDeadline.stop();
        downloadActive = false;
        if (downloadReply) {
            auto* reply = downloadReply.data();
            downloadReply.clear();
            reply->disconnect(&q);
            reply->abort();
            reply->deleteLater();
        }
        if (packageFile.isOpen())
            packageFile.close();
        if (removePartial) {
            if (!packagePartPath.isEmpty())
                QFile::remove(packagePartPath);
            if (!checksumPartPath.isEmpty())
                QFile::remove(checksumPartPath);
        }
        downloadStage = DownloadStage::None;
        downloadReceived = 0;
        downloadTotal = 0;
    }

    void downloadFailure(const char* error) {
        stopDownload(true);
        const bool restoreAvailable = !downloadManual && hasDownloadPrevious;
        hasDownloadPrevious = false;
        downloadManual = false;
        if (restoreAvailable) {
            status = downloadPrevious;
            status.received = status.total = 0;
            errorSource.clear();
            errorContext = QByteArrayLiteral("UpdateService");
        } else {
            errorSource = error;
            errorContext = QByteArrayLiteral("UpdateErrors");
            status.state = UpdateState::Failed;
            status.error = QCoreApplication::translate(errorContext.constData(), error);
        }
        emit q.statusChanged();
        emit q.operationFinished(QStringLiteral("download"), QStringLiteral("failed"));
    }

    void consumeDownload() {
        if (!downloadReply)
            return;
        const QByteArray bytes = downloadReply->readAll();
        if (bytes.isEmpty())
            return;
        if (downloadStage == DownloadStage::Package) {
            if (downloadReceived + bytes.size() > MAXIMUM_PACKAGE_BYTES ||
                packageFile.write(bytes) != bytes.size()) {
                downloadFailure(
                    QT_TRANSLATE_NOOP("UpdateErrors", "Could not save the update package"));
                return;
            }
        } else if (downloadStage == DownloadStage::Checksum) {
            if (checksumBytes.size() + bytes.size() > MAXIMUM_CHECKSUM_BYTES) {
                downloadFailure(QT_TRANSLATE_NOOP("UpdateErrors", "Invalid update checksum"));
                return;
            }
            checksumBytes += bytes;
        }
        downloadReceived += bytes.size();
        status.received = downloadReceived;
        emit q.statusChanged();
    }

    void requestDownload(const QUrl& url, DownloadStage stage) {
        if (!validUrl(url)) {
            downloadFailure(QT_TRANSLATE_NOOP("UpdateErrors", "The update server must use HTTPS"));
            return;
        }
        downloadStage = stage;
        downloadReceived = 0;
        downloadTotal = 0;
        status.received = 0;
        status.total = 0;
        QNetworkRequest request(url);
        request.setAttribute(QNetworkRequest::RedirectPolicyAttribute,
                             QNetworkRequest::SameOriginRedirectPolicy);
        request.setAttribute(QNetworkRequest::CacheLoadControlAttribute,
                             QNetworkRequest::AlwaysNetwork);
        request.setRawHeader("User-Agent", "SnowShot/" + options.installedVersion.toUtf8());
        request.setRawHeader("Cache-Control", "no-cache");
        downloadActive = true;
        downloadReply = network.get(request);
        downloadReply->setReadBufferSize(256 * 1024);
        const QPointer<QNetworkReply> current = downloadReply;
        QObject::connect(downloadReply, &QNetworkReply::metaDataChanged, &q, [this, current] {
            if (downloadReply != current || !downloadReply)
                return;
            const qint64 length =
                downloadReply->header(QNetworkRequest::ContentLengthHeader).toLongLong();
            if (length > MAXIMUM_PACKAGE_BYTES) {
                downloadFailure(QT_TRANSLATE_NOOP("UpdateErrors", "Update payload is too large"));
                return;
            }
            if (length < 0)
                return;
            downloadTotal = length;
            status.total = length;
            emit q.statusChanged();
        });
        QObject::connect(downloadReply, &QNetworkReply::readyRead, &q, [this, current] {
            if (downloadReply == current)
                consumeDownload();
        });
        QObject::connect(downloadReply, &QNetworkReply::finished, &q, [this, current] {
            if (downloadReply != current)
                return;
            consumeDownload();
            if (!downloadReply || downloadReply != current || !downloadActive)
                return;
            const bool successful =
                downloadReply->error() == QNetworkReply::NoError &&
                downloadReply->attribute(QNetworkRequest::HttpStatusCodeAttribute).toInt() == 200;
            if (!successful) {
                downloadFailure(QT_TRANSLATE_NOOP("UpdateErrors",
                                                  "The update package could not be downloaded"));
                return;
            }
            downloadReply->deleteLater();
            downloadReply.clear();
            downloadDeadline.stop();
            if (downloadStage == DownloadStage::Package) {
                packageFile.close();
                QFile::remove(packagePath);
                if (!QFile::rename(packagePartPath, packagePath)) {
                    downloadFailure(
                        QT_TRANSLATE_NOOP("UpdateErrors", "Could not save the verified update"));
                    return;
                }
                checksumBytes.clear();
                downloadStage = DownloadStage::Checksum;
                status.received = 0;
                status.total = 0;
                emit q.statusChanged();
                requestDownload(checksumUrl, DownloadStage::Checksum);
                return;
            }
            QSaveFile checksumFile(checksumPartPath);
            if (!checksumFile.open(QIODevice::WriteOnly) ||
                checksumFile.write(checksumBytes) != checksumBytes.size() ||
                !checksumFile.commit()) {
                downloadFailure(
                    QT_TRANSLATE_NOOP("UpdateErrors", "Could not save the verified update"));
                return;
            }
            QFile file(packagePath);
            if (!file.open(QIODevice::ReadOnly)) {
                downloadFailure(QT_TRANSLATE_NOOP("UpdateErrors", "Could not read update payload"));
                return;
            }
            QCryptographicHash hasher(QCryptographicHash::Sha256);
            while (!file.atEnd()) {
                const QByteArray chunk = file.read(1024 * 1024);
                if (chunk.isEmpty() && !file.atEnd()) {
                    downloadFailure(
                        QT_TRANSLATE_NOOP("UpdateErrors", "Could not read update payload"));
                    return;
                }
                hasher.addData(chunk);
            }
            const QByteArray actual = hasher.result().toHex();
            file.close();
            const auto checksum =
                QRegularExpression(QStringLiteral("\\A([0-9A-Fa-f]{64})(?:\\s|\\z)"))
                    .match(QString::fromUtf8(checksumBytes).trimmed());
            if (!checksum.hasMatch() || checksum.captured(1).compare(QString::fromLatin1(actual),
                                                                     Qt::CaseInsensitive) != 0) {
                downloadFailure(QT_TRANSLATE_NOOP("UpdateErrors", "Invalid update checksum"));
                return;
            }
            stopDownload(false);
            hasDownloadPrevious = false;
            downloadManual = false;
            status.state = UpdateState::Ready;
            status.received = status.total = QFileInfo(packagePath).size();
            status.error.clear();
            errorSource.clear();
            errorContext = QByteArrayLiteral("UpdateService");
            emit q.statusChanged();
            emit q.operationFinished(QStringLiteral("download"), QStringLiteral("success"));
            emit q.updateReady();
        });
        QObject::connect(&downloadDeadline, &QTimer::timeout, &q, [this, current] {
            if (downloadReply == current)
                downloadFailure(
                    QT_TRANSLATE_NOOP("UpdateErrors", "The update download was interrupted"));
        });
        downloadDeadline.start(
            options.requestTimeout.count() > 0
                ? std::max(options.requestTimeout, std::chrono::milliseconds(30000))
                : std::chrono::minutes(10));
    }

    void download(bool user) {
        if (downloadActive || status.state != UpdateState::Available ||
            !parseVersion(status.version))
            return;
        downloadManual = user;
        downloadPrevious = status;
        hasDownloadPrevious = true;
        if (!validUrl(status.downloadUrl) || checksumUrl.isEmpty()) {
            downloadFailure(
                QT_TRANSLATE_NOOP("UpdateErrors", "The update package could not be downloaded"));
            return;
        }
        const QDir cache(updateCacheDirectory());
        if (!QDir().mkpath(cache.absolutePath())) {
            downloadFailure(QT_TRANSLATE_NOOP("UpdateErrors", "Could not create update cache"));
            return;
        }
        packagePath = cache.filePath(packageFileName(status.version));
        packagePartPath = packagePath + QStringLiteral(".part");
        checksumPartPath = packagePath + QStringLiteral(".sha256");
        QFile::remove(packagePartPath);
        packageFile.setFileName(packagePartPath);
        if (!packageFile.open(QIODevice::WriteOnly)) {
            downloadFailure(
                QT_TRANSLATE_NOOP("UpdateErrors", "Could not open the update download file"));
            return;
        }
        status.state = UpdateState::Downloading;
        status.error.clear();
        emit q.statusChanged();
        requestDownload(status.downloadUrl, DownloadStage::Package);
    }
    void check(bool user) {
        if (!user && mode == u"manual")
            return;
        if (busy()) {
            manual = manual || user;
            return;
        }
        schedule.stop();
        manual = user;
        previous = status;
        previousErrorSource = errorSource;
        errorSource.clear();
        if (!parseVersion(options.installedVersion) || !validUrl(options.githubApiUrl) ||
            !validUrl(options.giteeApiUrl)) {
            finishFailure(QT_TRANSLATE_NOOP("UpdateService",
                                            "Could not check for updates. Please try again."));
            return;
        }
        resetAll();
        status = {UpdateState::Checking, {}, {}, 0, 0};
        emit q.statusChanged();
        request(Source::GitHub);
        request(Source::Gitee);
    }

    UpdateService& q;
    Options options;
    QNetworkAccessManager network;
    QTimer schedule;
    QTimer downloadDeadline{&q};
    Channel github;
    Channel gitee;
    QPointer<QNetworkReply> downloadReply;
    QFile packageFile;
    QByteArray checksumBytes;
    DownloadStage downloadStage = DownloadStage::None;
    QString packagePath;
    QString packagePartPath;
    QString checksumPartPath;
    QUrl checksumUrl;
    qint64 downloadReceived = 0;
    qint64 downloadTotal = 0;
    QByteArray errorSource;
    QByteArray errorContext = QByteArrayLiteral("UpdateService");
    QByteArray previousErrorSource;
    UpdateStatus status;
    UpdateStatus previous;
    UpdateStatus downloadPrevious;
    QSet<QString> notified;
    QString mode = QStringLiteral("check");
    bool started = false;
    bool manual = false;
    bool downloadActive = false;
    bool hasDownloadPrevious = false;
    bool downloadManual = false;
};

UpdateService::UpdateService(Options options, QObject* parent)
    : QObject(parent), m_impl(std::make_unique<Impl>(*this, std::move(options))) {
    setObjectName(QStringLiteral("snowShotUpdateService"));
}
UpdateService::~UpdateService() {
    m_impl->stopDownload(true);
    m_impl->resetAll();
}
const UpdateStatus& UpdateService::status() const {
    return m_impl->status;
}
bool UpdateService::managedByStore() const {
    return false;
}
bool UpdateService::busy() const {
    return m_impl->busy();
}
void UpdateService::start() {
    if (m_impl->started)
        return;
    m_impl->started = true;
    m_impl->arm(m_impl->options.startupCheckDelay);
}
void UpdateService::setMode(const QString& value) {
    if ((value != u"manual" && value != u"check" && value != u"download") || value == m_impl->mode)
        return;
    m_impl->mode = value;
    if (value == u"manual") {
        m_impl->schedule.stop();
        const bool automaticCheck =
            (m_impl->github.active || m_impl->gitee.active) && !m_impl->manual;
        const bool automaticDownload = m_impl->downloadActive && !m_impl->downloadManual;
        if (automaticCheck || automaticDownload)
            cancel();
    } else {
        m_impl->arm(m_impl->options.startupCheckDelay);
        if (m_impl->automaticDownloadEnabled() && m_impl->status.state == UpdateState::Available)
            m_impl->download(false);
    }
}
void UpdateService::setSystemProxy(bool enabled) {
    if (enabled)
        m_impl->network.setProxyFactory(new SystemProxyFactory);
    else
        m_impl->network.setProxy(QNetworkProxy::NoProxy);
}
void UpdateService::check(bool manual) {
    m_impl->check(manual);
}
void UpdateService::cancel() {
    if (!m_impl->busy())
        return;
    if (m_impl->downloadActive) {
        m_impl->stopDownload(true);
        if (m_impl->hasDownloadPrevious)
            m_impl->status = m_impl->downloadPrevious;
        else
            m_impl->status.state = UpdateState::Idle;
        m_impl->hasDownloadPrevious = false;
        m_impl->downloadManual = false;
        m_impl->status.received = 0;
        m_impl->status.total = 0;
        emit statusChanged();
        emit operationFinished(QStringLiteral("download"), QStringLiteral("cancelled"));
        return;
    }
    m_impl->resetAll();
    m_impl->status = m_impl->previous;
    m_impl->errorSource = m_impl->previousErrorSource;
    m_impl->arm(m_impl->options.automaticCheckInterval);
    emit statusChanged();
    emit operationFinished(QStringLiteral("check"), QStringLiteral("cancelled"));
}
void UpdateService::download() {
    m_impl->download(true);
}
void UpdateService::requestRestart() {
    if (m_impl->status.state == UpdateState::Ready)
        emit restartRequested();
}
void UpdateService::beginApply() {
    if (m_impl->status.state != UpdateState::Ready || m_impl->packagePath.isEmpty())
        return;
    const QString script = QDir(m_impl->options.applicationDirectory)
                               .filePath(QStringLiteral("../Resources/install-snow-shot-macos.sh"));
    if (!QFileInfo::exists(script)) {
        m_impl->errorSource =
            QT_TRANSLATE_NOOP("UpdateErrors", "Could not launch the application update helper");
        m_impl->errorContext = QByteArrayLiteral("UpdateErrors");
        m_impl->status.state = UpdateState::Failed;
        m_impl->status.error = QCoreApplication::translate(m_impl->errorContext.constData(),
                                                           m_impl->errorSource.constData());
        emit statusChanged();
        emit operationFinished(QStringLiteral("apply"), QStringLiteral("failed"));
        return;
    }
    QDir bundleDirectory(m_impl->options.applicationDirectory);
    bundleDirectory.cdUp();
    bundleDirectory.cdUp();
    const QStringList arguments{script,
                                QStringLiteral("--dmg"),
                                m_impl->packagePath,
                                QStringLiteral("--wait-pid"),
                                QString::number(QCoreApplication::applicationPid()),
                                QStringLiteral("--destination"),
                                bundleDirectory.absolutePath()};
    if (!QProcess::startDetached(QStringLiteral("/bin/bash"), arguments)) {
        m_impl->errorSource =
            QT_TRANSLATE_NOOP("UpdateErrors", "Could not launch the application update helper");
        m_impl->errorContext = QByteArrayLiteral("UpdateErrors");
        m_impl->status.state = UpdateState::Failed;
        m_impl->status.error = QCoreApplication::translate(m_impl->errorContext.constData(),
                                                           m_impl->errorSource.constData());
        emit statusChanged();
        emit operationFinished(QStringLiteral("apply"), QStringLiteral("failed"));
        return;
    }
    m_impl->status.state = UpdateState::Applying;
    emit statusChanged();
    emit operationFinished(QStringLiteral("apply"), QStringLiteral("success"));
    emit handoffCommitted();
}
void UpdateService::applyAtStartup() {
    emit operationFinished(QStringLiteral("apply"), QStringLiteral("success"));
}
void UpdateService::setRelaunchArguments(const QStringList&) {}
void UpdateService::clearRelaunchArguments() {}
bool UpdateService::handoffPending() const {
    return false;
}
void UpdateService::setProgressAppearance(const QJsonObject&) {}
void UpdateService::reportBlocked(const QString&) {}
bool UpdateService::event(QEvent* event) {
    if (event->type() == QEvent::LanguageChange && !m_impl->errorSource.isEmpty()) {
        m_impl->status.error = QCoreApplication::translate(m_impl->errorContext.constData(),
                                                           m_impl->errorSource.constData());
        emit statusChanged();
    }
    return QObject::event(event);
}
} // namespace snow_shot::update
