package com.generalsx.zerohour;

import android.content.Context;
import android.content.SharedPreferences;
import android.content.pm.PackageInfo;
import android.util.Base64;
import android.util.Log;

import org.json.JSONObject;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.HttpURLConnection;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.security.KeyFactory;
import java.security.MessageDigest;
import java.security.PublicKey;
import java.security.Signature;
import java.security.spec.X509EncodedKeySpec;
import java.util.Iterator;
import java.util.zip.GZIPInputStream;

/**
 * GeneralsX @feature Android port 27/09/2026 Updates without reinstalling the APK.
 *
 * The repository's {@code updates} branch holds one commit: {@code manifest.json}, its signature
 * {@code manifest.json.sig}, and, when there is one, a newer engine ({@code engine/<seq>/
 * libmain.so.gz}, {@code libmain60.so.gz}). The launcher fetches the manifest, and uses it only if
 *
 * <ul>
 *   <li>the signature verifies against {@link #PUBLIC_KEY_B64} (ECDSA P-256 over the exact bytes;
 *       the private key never enters the repository -- see docs/HOWTO/PUBLISH_UPDATE.md), and</li>
 *   <li>its {@code serial} is not lower than the last one accepted, so an old signed manifest
 *       cannot be replayed to roll players back.</li>
 * </ul>
 *
 * Nothing is secret here: the manifest is public, and so are the service addresses in it. What
 * the signature guards against is substitution -- a changed file, whether on the way or in the
 * repository, is refused.
 *
 * What a verified manifest can carry:
 * <ul>
 *   <li>{@code config}: string values written to {@code files/update/remote_config.ini}, read by
 *       the engine at startup (GXRemoteConfig.h) -- today the STUN and TURN server lists.</li>
 *   <li>{@code engine}: a newer engine build. Its files are downloaded, checked against the
 *       SHA-256 in the (signed) manifest, and loaded instead of the APK's own by
 *       {@link GeneralsZHActivity} -- but only when its {@code seq} is higher than the APK's
 *       bundled engine (assets/engine_build.txt, the commit count it was built at) and the
 *       libraries it was linked against ({@code requires_libs}) are exactly the ones this APK
 *       installed. An engine that twice fails to reach the main menu is dropped
 *       ({@link #noteEngineBoot}).</li>
 * </ul>
 */
final class UpdateManager {
    private static final String TAG = "GXUpdate";

    static final String BASE_URL =
        "https://raw.githubusercontent.com/MYSOREZ/GeneralsZH-Android-Port/updates/";

    /** SubjectPublicKeyInfo (DER, base64) of the update signing key. */
    static final String PUBLIC_KEY_B64 =
        "MFkwEwYHKoZIzj0CAQYIKoZIzj0DAQcDQgAEFjy+4K0lTRmnwQe+nQqXreCMtJehCl1wiYNgq5Rr/MHWkDukps0eUbmuyxSenyFL4T5zo+WBIFeLDO5PXFoG/A==";

    static final String[] ENGINE_LIBS = { "libmain.so", "libmain60.so" };

    private static final String PREFS = "gx_update";
    private static final String KEY_SERIAL = "serial";
    private static final String KEY_AUTO = "auto_check";
    private static final String KEY_LAST_CHECK = "last_check";
    private static final String KEY_DEPS_OK_FOR = "deps_ok_for";

    private UpdateManager() {
    }

    // ---------------------------------------------------------------------------------------
    // Paths

    static File updateDir(Context ctx) {
        return new File(ctx.getFilesDir(), "update");
    }

    private static File engineRoot(Context ctx) {
        return new File(updateDir(ctx), "engine");
    }

    private static File activeEngineMarker(Context ctx) {
        return new File(updateDir(ctx), "engine_active.txt");
    }

    /** Written before an updated engine is loaded, deleted by the engine at its main menu. */
    private static File bootPendingMarker(Context ctx) {
        return new File(updateDir(ctx), "boot_pending");
    }

    private static File badEngineMarker(Context ctx) {
        return new File(updateDir(ctx), "engine_bad.txt");
    }

    // ---------------------------------------------------------------------------------------
    // Settings

    static boolean isAutoCheckEnabled(Context ctx) {
        return prefs(ctx).getBoolean(KEY_AUTO, true);
    }

    static void setAutoCheckEnabled(Context ctx, boolean enabled) {
        prefs(ctx).edit().putBoolean(KEY_AUTO, enabled).apply();
    }

    static long lastCheckMillis(Context ctx) {
        return prefs(ctx).getLong(KEY_LAST_CHECK, 0L);
    }

    static int acceptedSerial(Context ctx) {
        return prefs(ctx).getInt(KEY_SERIAL, 0);
    }

    private static SharedPreferences prefs(Context ctx) {
        return ctx.getSharedPreferences(PREFS, Context.MODE_PRIVATE);
    }

    // ---------------------------------------------------------------------------------------
    // Engine selection (called by GeneralsZHActivity before SDL loads the libraries)

    /** The commit count the APK's own engine was built at; 0 if the APK does not say. */
    static int bundledEngineSeq(Context ctx) {
        try (InputStream in = ctx.getAssets().open("engine_build.txt")) {
            String text = new String(readAll(in), StandardCharsets.US_ASCII).trim();
            return Integer.parseInt(text);
        } catch (IOException | NumberFormatException e) {
            return 0;
        }
    }

    /** The downloaded engine that is ready to run, or 0 if the APK's own engine should run. */
    static int activeEngineSeq(Context ctx) {
        int seq = readInt(activeEngineMarker(ctx));
        if (seq <= 0 || seq <= bundledEngineSeq(ctx) || seq == readInt(badEngineMarker(ctx))) {
            return 0;
        }
        for (String lib : ENGINE_LIBS) {
            if (!new File(new File(engineRoot(ctx), Integer.toString(seq)), lib).isFile()) {
                return 0;
            }
        }
        if (!dependenciesStillMatch(ctx, seq)) {
            return 0;
        }
        return seq;
    }

    /** Absolute path of an updated engine library, or null to load the APK's own. */
    static String activeEngineLibrary(Context ctx, String libName) {
        int seq = activeEngineSeq(ctx);
        if (seq == 0) {
            return null;
        }
        return new File(new File(engineRoot(ctx), Integer.toString(seq)), libName).getAbsolutePath();
    }

    /**
     * Record that an updated engine is about to start. If the marker is still there from the
     * previous start of the same engine -- it never reached the main menu -- count it; on the
     * second such failure the engine is marked bad and the APK's own runs from then on.
     * @return true if the updated engine may be used for this start.
     */
    static boolean noteEngineBoot(Context ctx, int seq) {
        File pending = bootPendingMarker(ctx);
        int failures = 0;
        if (pending.isFile()) {
            String[] parts = readText(pending).trim().split(" ");
            if (parts.length == 2 && Integer.toString(seq).equals(parts[0])) {
                try {
                    failures = Integer.parseInt(parts[1]) + 1;
                } catch (NumberFormatException ignored) {
                    failures = 1;
                }
            }
        }
        if (failures >= 2) {
            Log.w(TAG, "engine " + seq + " failed to reach the main menu twice; using the APK's engine");
            writeText(badEngineMarker(ctx), Integer.toString(seq));
            pending.delete();
            return false;
        }
        writeText(pending, seq + " " + failures);
        return true;
    }

    // ---------------------------------------------------------------------------------------
    // Checking

    static final class Result {
        boolean ok;
        String error;
        int serial;
        boolean configUpdated;
        int engineSeq;              // engine offered by the manifest, 0 if none
        boolean engineDownloaded;   // newly downloaded and ready for the next start
        boolean engineIncompatible; // offered but built against other libraries -- needs a new APK
        boolean offline;            // no network: nothing changed, the last good update stays in use
    }

    /** Blocking; call off the UI thread. */
    static Result check(Context ctx) {
        Result r = new Result();
        try {
            byte[] manifestBytes = download(BASE_URL + "manifest.json", 256 * 1024);
            byte[] signatureText = download(BASE_URL + "manifest.json.sig", 16 * 1024);
            if (!verify(manifestBytes, signatureText)) {
                r.error = "signature";
                return r;
            }
            JSONObject manifest = new JSONObject(new String(manifestBytes, StandardCharsets.UTF_8));
            r.serial = manifest.optInt("serial", 0);
            if (r.serial < acceptedSerial(ctx)) {
                r.error = "older manifest (" + r.serial + " < " + acceptedSerial(ctx) + ")";
                return r;
            }

            File dir = updateDir(ctx);
            if (!dir.isDirectory() && !dir.mkdirs()) {
                r.error = "cannot create " + dir;
                return r;
            }

            JSONObject config = manifest.optJSONObject("config");
            if (config != null) {
                r.configUpdated = writeRemoteConfig(ctx, config);
            }

            JSONObject engine = manifest.optJSONObject("engine");
            if (engine != null) {
                applyEngine(ctx, engine, r);
            }

            writeBytes(new File(dir, "manifest.json"), manifestBytes);
            prefs(ctx).edit()
                .putInt(KEY_SERIAL, r.serial)
                .putLong(KEY_LAST_CHECK, System.currentTimeMillis())
                .apply();
            r.ok = r.error == null;
        } catch (java.net.UnknownHostException | java.net.ConnectException
                 | java.net.SocketTimeoutException | java.net.NoRouteToHostException e) {
            // Offline is a normal state, not an error: the launcher and the game work without a
            // network, and whatever was verified last time (settings, engine) stays in use.
            r.offline = true;
            r.error = "offline";
        } catch (Exception e) {
            Log.w(TAG, "update check failed", e);
            String msg = e.getMessage();
            r.error = (msg == null || msg.isEmpty()) ? e.getClass().getSimpleName() : msg;
        }
        return r;
    }

    private static boolean writeRemoteConfig(Context ctx, JSONObject config) throws IOException {
        StringBuilder ini = new StringBuilder();
        ini.append("# Written by the launcher from a signed update manifest. Do not edit.\n");
        for (Iterator<String> it = config.keys(); it.hasNext(); ) {
            String key = it.next();
            String value = config.optString(key, "");
            if (!key.matches("[a-z0-9_]+") || value.indexOf('\n') >= 0) {
                continue;
            }
            ini.append(key).append('=').append(value).append('\n');
        }
        File file = new File(updateDir(ctx), "remote_config.ini");
        String before = file.isFile() ? readText(file) : "";
        String after = ini.toString();
        if (before.equals(after)) {
            return false;
        }
        writeBytes(file, after.getBytes(StandardCharsets.UTF_8));
        return true;
    }

    private static void applyEngine(Context ctx, JSONObject engine, Result r) throws Exception {
        int seq = engine.optInt("seq", 0);
        r.engineSeq = seq;
        if (seq <= bundledEngineSeq(ctx) || seq == readInt(badEngineMarker(ctx))) {
            return;
        }
        JSONObject requires = engine.optJSONObject("requires_libs");
        if (requires == null || !librariesMatch(ctx, requires)) {
            r.engineIncompatible = true;
            return;
        }
        File target = new File(engineRoot(ctx), Integer.toString(seq));
        JSONObject files = engine.getJSONObject("files");
        boolean all = true;
        for (String lib : ENGINE_LIBS) {
            JSONObject entry = files.optJSONObject(lib);
            if (entry == null) {
                all = false;
                break;
            }
            File out = new File(target, lib);
            String sha = entry.getString("sha256");
            if (out.isFile() && sha.equalsIgnoreCase(sha256(out))) {
                continue;
            }
            downloadEngineFile(entry.getString("url"), entry.optLong("size", 0L), sha, out);
        }
        if (!all) {
            r.error = "engine entry is missing a library";
            return;
        }
        boolean wasActive = readInt(activeEngineMarker(ctx)) == seq;
        writeText(activeEngineMarker(ctx), Integer.toString(seq));
        prefs(ctx).edit().putString(KEY_DEPS_OK_FOR, depsStamp(ctx, seq)).apply();
        pruneOtherEngines(ctx, seq);
        r.engineDownloaded = !wasActive;
    }

    // ---------------------------------------------------------------------------------------
    // Library compatibility

    private static boolean librariesMatch(Context ctx, JSONObject requires) throws IOException {
        File libDir = new File(ctx.getApplicationInfo().nativeLibraryDir);
        for (Iterator<String> it = requires.keys(); it.hasNext(); ) {
            String lib = it.next();
            File installed = new File(libDir, lib);
            if (!installed.isFile() || !requires.optString(lib, "").equalsIgnoreCase(sha256(installed))) {
                Log.i(TAG, "engine needs a different " + lib + " than this APK installed");
                return false;
            }
        }
        return true;
    }

    /** Re-checked after the APK itself is updated, since that replaces the libraries. */
    private static boolean dependenciesStillMatch(Context ctx, int seq) {
        String stamp = depsStamp(ctx, seq);
        if (stamp.equals(prefs(ctx).getString(KEY_DEPS_OK_FOR, ""))) {
            return true;
        }
        try {
            File manifestFile = new File(updateDir(ctx), "manifest.json");
            JSONObject engine = new JSONObject(readText(manifestFile)).optJSONObject("engine");
            if (engine == null || engine.optInt("seq", 0) != seq) {
                return false;
            }
            JSONObject requires = engine.optJSONObject("requires_libs");
            if (requires != null && librariesMatch(ctx, requires)) {
                prefs(ctx).edit().putString(KEY_DEPS_OK_FOR, stamp).apply();
                return true;
            }
        } catch (Exception e) {
            Log.w(TAG, "could not re-check the engine's libraries", e);
        }
        return false;
    }

    private static String depsStamp(Context ctx, int seq) {
        long installed = 0L;
        try {
            PackageInfo info = ctx.getPackageManager().getPackageInfo(ctx.getPackageName(), 0);
            installed = info.lastUpdateTime;
        } catch (Exception ignored) {
            // an unknown install time just forces a re-check
        }
        return seq + ":" + installed;
    }

    private static void pruneOtherEngines(Context ctx, int keep) {
        File[] dirs = engineRoot(ctx).listFiles();
        if (dirs == null) {
            return;
        }
        for (File d : dirs) {
            if (d.isDirectory() && !d.getName().equals(Integer.toString(keep))) {
                File[] files = d.listFiles();
                if (files != null) {
                    for (File f : files) {
                        f.delete();
                    }
                }
                d.delete();
            }
        }
    }

    // ---------------------------------------------------------------------------------------
    // Crypto and transfer

    static boolean verify(byte[] data, byte[] signatureText) {
        try {
            byte[] keyBytes = Base64.decode(PUBLIC_KEY_B64, Base64.DEFAULT);
            PublicKey key = KeyFactory.getInstance("EC").generatePublic(new X509EncodedKeySpec(keyBytes));
            byte[] sig = Base64.decode(new String(signatureText, StandardCharsets.US_ASCII).trim(), Base64.DEFAULT);
            Signature verifier = Signature.getInstance("SHA256withECDSA");
            verifier.initVerify(key);
            verifier.update(data);
            return verifier.verify(sig);
        } catch (Exception e) {
            Log.w(TAG, "signature check failed", e);
            return false;
        }
    }

    private static byte[] download(String url, int maxBytes) throws IOException {
        HttpURLConnection conn = open(url);
        try (InputStream in = conn.getInputStream()) {
            ByteArrayOutputStream out = new ByteArrayOutputStream();
            byte[] buf = new byte[16384];
            int n;
            while ((n = in.read(buf)) > 0) {
                out.write(buf, 0, n);
                if (out.size() > maxBytes) {
                    throw new IOException("response too large: " + url);
                }
            }
            return out.toByteArray();
        } finally {
            conn.disconnect();
        }
    }

    /** Downloads a .gz, inflates it to a temp file, checks size and SHA-256, then moves it in. */
    private static void downloadEngineFile(String url, long size, String sha256, File out) throws Exception {
        File parent = out.getParentFile();
        if (parent != null && !parent.isDirectory() && !parent.mkdirs()) {
            throw new IOException("cannot create " + parent);
        }
        File tmp = new File(out.getPath() + ".part");
        HttpURLConnection conn = open(url);
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        long written = 0;
        try (InputStream raw = conn.getInputStream();
             InputStream in = url.endsWith(".gz") ? new GZIPInputStream(raw, 65536) : raw;
             OutputStream os = new FileOutputStream(tmp)) {
            byte[] buf = new byte[65536];
            int n;
            while ((n = in.read(buf)) > 0) {
                os.write(buf, 0, n);
                digest.update(buf, 0, n);
                written += n;
                if (size > 0 && written > size) {
                    throw new IOException("engine file larger than the manifest says");
                }
            }
        } finally {
            conn.disconnect();
        }
        String got = hex(digest.digest());
        if ((size > 0 && written != size) || !got.equalsIgnoreCase(sha256)) {
            tmp.delete();
            throw new IOException("engine file does not match the signed manifest: " + out.getName());
        }
        if (out.exists() && !out.delete()) {
            tmp.delete();
            throw new IOException("cannot replace " + out);
        }
        if (!tmp.renameTo(out)) {
            tmp.delete();
            throw new IOException("cannot move " + tmp + " to " + out);
        }
    }

    private static HttpURLConnection open(String url) throws IOException {
        HttpURLConnection conn = (HttpURLConnection) new URL(url).openConnection();
        conn.setConnectTimeout(15000);
        conn.setReadTimeout(60000);
        conn.setUseCaches(false);
        int status = conn.getResponseCode();
        if (status < 200 || status >= 300) {
            conn.disconnect();
            throw new IOException("HTTP " + status + " for " + url);
        }
        return conn;
    }

    static String sha256(File file) throws IOException {
        try (InputStream in = new FileInputStream(file)) {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] buf = new byte[65536];
            int n;
            while ((n = in.read(buf)) > 0) {
                digest.update(buf, 0, n);
            }
            return hex(digest.digest());
        } catch (java.security.NoSuchAlgorithmException e) {
            throw new IOException(e);
        }
    }

    private static String hex(byte[] bytes) {
        StringBuilder sb = new StringBuilder(bytes.length * 2);
        for (byte b : bytes) {
            sb.append(String.format(java.util.Locale.ROOT, "%02x", b & 0xff));
        }
        return sb.toString();
    }

    // ---------------------------------------------------------------------------------------
    // Small file helpers

    private static byte[] readAll(InputStream in) throws IOException {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        byte[] buf = new byte[8192];
        int n;
        while ((n = in.read(buf)) > 0) {
            out.write(buf, 0, n);
        }
        return out.toByteArray();
    }

    private static String readText(File file) {
        try (InputStream in = new FileInputStream(file)) {
            return new String(readAll(in), StandardCharsets.UTF_8);
        } catch (IOException e) {
            return "";
        }
    }

    private static int readInt(File file) {
        try {
            return file.isFile() ? Integer.parseInt(readText(file).trim()) : 0;
        } catch (NumberFormatException e) {
            return 0;
        }
    }

    private static void writeText(File file, String text) {
        try {
            writeBytes(file, text.getBytes(StandardCharsets.UTF_8));
        } catch (IOException e) {
            Log.w(TAG, "cannot write " + file, e);
        }
    }

    private static void writeBytes(File file, byte[] bytes) throws IOException {
        File parent = file.getParentFile();
        if (parent != null && !parent.isDirectory() && !parent.mkdirs()) {
            throw new IOException("cannot create " + parent);
        }
        File tmp = new File(file.getPath() + ".tmp");
        try (OutputStream out = new FileOutputStream(tmp)) {
            out.write(bytes);
        }
        if (!tmp.renameTo(file)) {
            file.delete();
            if (!tmp.renameTo(file)) {
                throw new IOException("cannot write " + file);
            }
        }
    }
}
