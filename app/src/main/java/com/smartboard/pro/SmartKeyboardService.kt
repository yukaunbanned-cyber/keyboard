package com.smartboard.pro

import android.content.ClipData
import android.content.ClipboardManager
import android.content.Context
import android.content.SharedPreferences
import android.graphics.Color
import android.graphics.Typeface
import android.graphics.drawable.GradientDrawable
import android.inputmethodservice.InputMethodService
import android.media.AudioManager
import android.media.ToneGenerator
import android.os.Build
import android.os.Handler
import android.os.Looper
import android.os.VibrationEffect
import android.os.Vibrator
import android.text.InputType
import android.text.TextUtils
import android.util.TypedValue
import android.view.Gravity
import android.view.KeyEvent
import android.view.MotionEvent
import android.view.View
import android.view.ViewGroup
import android.view.inputmethod.EditorInfo
import android.view.inputmethod.ExtractedTextRequest
import android.widget.FrameLayout
import android.widget.HorizontalScrollView
import android.widget.LinearLayout
import android.widget.ScrollView
import android.widget.TextView
import android.widget.Toast
import org.json.JSONArray
import org.json.JSONObject
import java.io.BufferedReader
import java.io.InputStreamReader
import java.net.HttpURLConnection
import java.net.URL
import java.net.URLEncoder
import java.text.SimpleDateFormat
import java.util.Date
import java.util.Locale
import java.util.concurrent.Executors
import kotlin.math.abs

class SmartKeyboardService : InputMethodService() {

    companion object {
        const val PREFS_NAME = "smartboard_pro_prefs"
        const val KEY_THEME = "theme_index"
        const val KEY_HEIGHT = "height_index"
        const val KEY_SOUND = "sound_mode"
        const val KEY_VIBRATE = "vibrate_enabled"
        const val KEY_CLIPS = "clipboard_history_json"
        const val KEY_AUTOTEXT = "autotext_templates_json"
    }

    data class KeyboardTheme(
        val name: String,
        val boardBg: Int,
        val toolbarBg: Int,
        val keyBg: Int,
        val specialKeyBg: Int,
        val accentColor: Int,
        val keyText: Int,
        val mutedText: Int,
        val borderColor: Int
    )

    data class ClipEntry(
        val text: String,
        var pinned: Boolean,
        val time: String
    )

    private val themes = listOf(
        KeyboardTheme(
            name = "Dark OLED",
            boardBg = Color.parseColor("#0A0D12"),
            toolbarBg = Color.parseColor("#121722"),
            keyBg = Color.parseColor("#1E2638"),
            specialKeyBg = Color.parseColor("#151C2B"),
            accentColor = Color.parseColor("#3B82F6"),
            keyText = Color.parseColor("#F8FAFC"),
            mutedText = Color.parseColor("#94A3B8"),
            borderColor = Color.parseColor("#2A364F")
        ),
        KeyboardTheme(
            name = "Cyber Neon RGB",
            boardBg = Color.parseColor("#090414"),
            toolbarBg = Color.parseColor("#140B29"),
            keyBg = Color.parseColor("#1F113D"),
            specialKeyBg = Color.parseColor("#150A2B"),
            accentColor = Color.parseColor("#00F5D4"),
            keyText = Color.parseColor("#FFFFFF"),
            mutedText = Color.parseColor("#C77DFF"),
            borderColor = Color.parseColor("#7209B7")
        ),
        KeyboardTheme(
            name = "Classic Light",
            boardBg = Color.parseColor("#D4D8E2"),
            toolbarBg = Color.parseColor("#E2E6F0"),
            keyBg = Color.parseColor("#FFFFFF"),
            specialKeyBg = Color.parseColor("#BAC2D4"),
            accentColor = Color.parseColor("#2563EB"),
            keyText = Color.parseColor("#0F172A"),
            mutedText = Color.parseColor("#475569"),
            borderColor = Color.parseColor("#94A3B8")
        ),
        KeyboardTheme(
            name = "Shopee Orange",
            boardBg = Color.parseColor("#120C0A"),
            toolbarBg = Color.parseColor("#1F1410"),
            keyBg = Color.parseColor("#2E1E19"),
            specialKeyBg = Color.parseColor("#211512"),
            accentColor = Color.parseColor("#EE4D2D"),
            keyText = Color.parseColor("#FFF7ED"),
            mutedText = Color.parseColor("#FDBA74"),
            borderColor = Color.parseColor("#7C2D12")
        )
    )

    private lateinit var prefs: SharedPreferences
    private var clipboardManager: ClipboardManager? = null
    private var toneGenerator: ToneGenerator? = null
    private var vibrator: Vibrator? = null
    private val uiHandler = Handler(Looper.getMainLooper())
    private val ioExecutor = Executors.newSingleThreadExecutor()

    // State
    private var themeIndex = 0
    private var heightIndex = 1 // 0=Compact, 1=Normal, 2=Tall
    private var soundMode = 0   // 0=Click, 1=Bubble, 2=Silent
    private var vibrateEnabled = true

    private var activeTab = "KEYS" // KEYS, TRANSLATE, CLIPBOARD, AUTOTEXT, CALC, EMOJI, THEME
    private var isSymbolLayer = false
    private var isShiftActive = false
    private var isCapsLock = false
    private var lastShiftTapTime = 0L

    // Live Translate buffer (allows typing directly with SmartBoard into Translate Bar)
    private var translateBuffer = StringBuilder()
    private var isTypingToTranslateBar = false
    private var selectedLangPair = "id|en"
    private var isTranslating = false

    // Calculator state
    private var calcExpression = StringBuilder()
    private var calcResultPreview = "0"

    // Emoji sub-tab
    private var emojiSubTab = 0 // 0=Emoji, 1=Kaomoji, 2=Simbol

    // Data lists
    private val clipList = mutableListOf<ClipEntry>()
    private val autoTextList = mutableListOf<String>()

    // UI Root references
    private var rootContainer: LinearLayout? = null
    private var keyPreviewBanner: TextView? = null
    private var translateInputDisplay: TextView? = null
    private var translateStatusText: TextView? = null

    // Backspace repeat runnable
    private var isBackspaceHeld = false
    private val backspaceRunnable = object : Runnable {
        override fun run() {
            if (isBackspaceHeld) {
                handleBackspace()
                playKeyFeedback()
                uiHandler.postDelayed(this, 65L)
            }
        }
    }

    private val clipListener = ClipboardManager.OnPrimaryClipChangedListener {
        try {
            val clip: ClipData? = clipboardManager?.primaryClip
            if (clip != null && clip.itemCount > 0) {
                val copiedText = clip.getItemAt(0).coerceToText(this)?.toString()?.trim() ?: ""
                if (copiedText.isNotEmpty()) {
                    addClipEntry(copiedText)
                }
            }
        } catch (_: Exception) {}
    }

    override fun onCreate() {
        super.onCreate()
        prefs = getSharedPreferences(PREFS_NAME, Context.MODE_PRIVATE)
        loadPreferences()

        try {
            toneGenerator = ToneGenerator(AudioManager.STREAM_MUSIC, 75)
        } catch (_: Exception) {
            toneGenerator = null
        }

        vibrator = getSystemService(Context.VIBRATOR_SERVICE) as? Vibrator

        clipboardManager = getSystemService(Context.CLIPBOARD_SERVICE) as? ClipboardManager
        clipboardManager?.addPrimaryClipChangedListener(clipListener)
    }

    override fun onDestroy() {
        super.onDestroy()
        try {
            clipboardManager?.removePrimaryClipChangedListener(clipListener)
            toneGenerator?.release()
            ioExecutor.shutdownNow()
        } catch (_: Exception) {}
    }

    override fun onCreateInputView(): View {
        loadPreferences()
        val root = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            layoutParams = ViewGroup.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.WRAP_CONTENT
            )
        }
        rootContainer = root
        renderFullKeyboardUI()
        return root
    }

    override fun onStartInputView(info: EditorInfo?, restarting: Boolean) {
        super.onStartInputView(info, restarting)
        loadPreferences()
        renderFullKeyboardUI()
    }

    private fun loadPreferences() {
        themeIndex = prefs.getInt(KEY_THEME, 0).coerceIn(0, themes.lastIndex)
        heightIndex = prefs.getInt(KEY_HEIGHT, 1).coerceIn(0, 2)
        soundMode = prefs.getInt(KEY_SOUND, 0).coerceIn(0, 2)
        vibrateEnabled = prefs.getBoolean(KEY_VIBRATE, true)

        // Load Clips
        clipList.clear()
        val clipsRaw = prefs.getString(KEY_CLIPS, null)
        if (!clipsRaw.isNullOrEmpty()) {
            try {
                val arr = JSONArray(clipsRaw)
                for (i in 0 until arr.length()) {
                    val obj = arr.getJSONObject(i)
                    clipList.add(
                        ClipEntry(
                            text = obj.optString("text", ""),
                            pinned = obj.optBoolean("pinned", false),
                            time = obj.optString("time", "Baru")
                        )
                    )
                }
            } catch (_: Exception) {}
        }
        if (clipList.isEmpty()) {
            clipList.add(ClipEntry("DANA: 0812-3456-7890 a/n Admin SmartBoard", true, "Default"))
            clipList.add(ClipEntry("Terima kasih! Pesanan Anda sedang kami proses sekarang.", false, "Default"))
            saveClipsToPrefs()
        }

        // Load Auto-Text
        autoTextList.clear()
        val autoRaw = prefs.getString(KEY_AUTOTEXT, null)
        if (!autoRaw.isNullOrEmpty()) {
            try {
                val arr = JSONArray(autoRaw)
                for (i in 0 until arr.length()) {
                    val item = arr.optString(i, "")
                    if (item.isNotEmpty()) autoTextList.add(item)
                }
            } catch (_: Exception) {}
        }
        if (autoTextList.isEmpty()) {
            autoTextList.addAll(
                listOf(
                    "Halo kak, barang ready stok siap kirim hari ini! 🚀",
                    "Pembayaran QRIS / DANA: 0812-3456-7890 (Wajib sertakan kode unik).",
                    "Mohon ditunggu sebentar ya kak, sedang kami cek di sistem 🙏",
                    "Alamat Lengkap: Jl. Sudirman No. 88, Pekanbaru, Riau.",
                    "Siap kak, terima kasih banyak sudah berbelanja! ⭐"
                )
            )
            saveAutoTextToPrefs()
        }
    }

    private fun saveClipsToPrefs() {
        val arr = JSONArray()
        clipList.forEach { c ->
            val obj = JSONObject()
            obj.put("text", c.text)
            obj.put("pinned", c.pinned)
            obj.put("time", c.time)
            arr.put(obj)
        }
        prefs.edit().putString(KEY_CLIPS, arr.toString()).apply()
    }

    private fun saveAutoTextToPrefs() {
        val arr = JSONArray()
        autoTextList.forEach { arr.put(it) }
        prefs.edit().putString(KEY_AUTOTEXT, arr.toString()).apply()
    }

    private fun addClipEntry(newText: String) {
        val existingIdx = clipList.indexOfFirst { it.text == newText }
        val wasPinned = if (existingIdx >= 0) clipList[existingIdx].pinned else false
        if (existingIdx >= 0) {
            clipList.removeAt(existingIdx)
        }
        val timeStr = SimpleDateFormat("HH:mm", Locale.getDefault()).format(Date())
        val entry = ClipEntry(newText, wasPinned, timeStr)
        val firstUnpinned = clipList.indexOfFirst { !it.pinned }
        if (wasPinned || firstUnpinned == -1) {
            clipList.add(0, entry)
        } else {
            clipList.add(firstUnpinned, entry)
        }
        while (clipList.size > 25) {
            clipList.removeLast()
        }
        saveClipsToPrefs()
        if (activeTab == "CLIPBOARD") {
            uiHandler.post { renderFullKeyboardUI() }
        }
    }

    // =========================================================================
    // MASTER UI RENDERER
    // =========================================================================
    private fun renderFullKeyboardUI() {
        val root = rootContainer ?: return
        root.removeAllViews()
        val theme = themes[themeIndex]
        root.setBackgroundColor(theme.boardBg)

        // 1. Top Toolbar Navigation + Key Preview Indicator
        root.addView(buildTopToolbar(theme))

        // 2. If Live Translate Mode is Active, show Translate Bar right above QWERTY keys!
        if (activeTab == "TRANSLATE") {
            root.addView(buildLiveTranslateBar(theme))
            root.addView(buildQwertyKeyboardArea(theme))
            return
        }

        // 3. Switchable Panel or Standard QWERTY Keyboard
        when (activeTab) {
            "KEYS" -> root.addView(buildQwertyKeyboardArea(theme))
            "CLIPBOARD" -> root.addView(buildClipboardPanel(theme))
            "AUTOTEXT" -> root.addView(buildAutoTextPanel(theme))
            "CALC" -> root.addView(buildCalculatorPanel(theme))
            "EMOJI" -> root.addView(buildEmojiPanel(theme))
            "THEME" -> root.addView(buildThemeSettingsPanel(theme))
            else -> root.addView(buildQwertyKeyboardArea(theme))
        }
    }

    private fun buildTopToolbar(theme: KeyboardTheme): View {
        val wrapper = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
            setBackgroundColor(theme.toolbarBg)
            setPadding(dp(6), dp(5), dp(6), dp(5))
            layoutParams = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                dp(44)
            )
        }

        val scroll = HorizontalScrollView(this).apply {
            isHorizontalScrollBarEnabled = false
            layoutParams = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
        }

        val row = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
        }

        val tabs = listOf(
            "KEYS" to "⌨️ Ketik",
            "TRANSLATE" to "🌍 Terjemah",
            "CLIPBOARD" to "📋 Klip (${clipList.size})",
            "AUTOTEXT" to "⚡ Auto-Text",
            "CALC" to "🧮 Kalkulator",
            "EMOJI" to "😀 Emoji",
            "THEME" to "🎨 Tema"
        )

        tabs.forEach { (id, label) ->
            val isSelected = activeTab == id
            val btn = TextView(this).apply {
                text = label
                setTextSize(TypedValue.COMPLEX_UNIT_SP, 12f)
                setTypeface(null, Typeface.BOLD)
                setTextColor(if (isSelected) Color.WHITE else theme.keyText)
                setPadding(dp(11), dp(6), dp(11), dp(6))
                background = roundedBg(
                    fillColor = if (isSelected) theme.accentColor else theme.keyBg,
                    strokeColor = if (isSelected) theme.accentColor else theme.borderColor,
                    radiusDp = 8
                )
                val lp = LinearLayout.LayoutParams(
                    ViewGroup.LayoutParams.WRAP_CONTENT,
                    ViewGroup.LayoutParams.WRAP_CONTENT
                )
                lp.setMargins(dp(3), 0, dp(3), 0)
                layoutParams = lp
                setOnClickListener {
                    playKeyFeedback()
                    activeTab = if (activeTab == id && id != "KEYS") "KEYS" else id
                    isTypingToTranslateBar = (activeTab == "TRANSLATE")
                    renderFullKeyboardUI()
                }
            }
            row.addView(btn)
        }

        scroll.addView(row)
        wrapper.addView(scroll)

        // Small Key Press Popup Indicator on the right of toolbar
        val previewBadge = TextView(this).apply {
            text = if (isCapsLock) "CAPS" else "PRO"
            setTextSize(TypedValue.COMPLEX_UNIT_SP, 11f)
            setTypeface(null, Typeface.BOLD)
            setTextColor(theme.accentColor)
            gravity = Gravity.CENTER
            setPadding(dp(8), dp(4), dp(8), dp(4))
            background = roundedBg(theme.specialKeyBg, theme.borderColor, 6)
        }
        keyPreviewBanner = previewBadge
        wrapper.addView(previewBadge)

        return wrapper
    }

    // =========================================================================
    // FEATURE 1: LIVE TRANSLATE BAR (WITH DIRECT QWERTY BUFFER + API)
    // =========================================================================
    private fun buildLiveTranslateBar(theme: KeyboardTheme): View {
        val container = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setBackgroundColor(theme.specialKeyBg)
            setPadding(dp(8), dp(6), dp(8), dp(6))
        }

        // Row 1: Language Pairs + Pull Chat Text button
        val langScroll = HorizontalScrollView(this).apply {
            isHorizontalScrollBarEnabled = false
        }
        val langRow = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
        }

        val pairs = listOf(
            "id|en" to "🇮🇩 ID ➔ 🇬🇧 EN",
            "en|id" to "🇬🇧 EN ➔ 🇮🇩 ID",
            "id|ja" to "🇮🇩 ID ➔ 🇯🇵 JA",
            "id|ar" to "🇮🇩 ID ➔ 🇸🇦 AR",
            "id|ko" to "🇮🇩 ID ➔ 🇰🇷 KO",
            "id|zh-CN" to "🇮🇩 ID ➔ 🇨🇳 ZH"
        )

        pairs.forEach { (code, title) ->
            val active = selectedLangPair == code
            val chip = TextView(this).apply {
                text = title
                setTextSize(TypedValue.COMPLEX_UNIT_SP, 11f)
                setTypeface(null, Typeface.BOLD)
                setTextColor(if (active) Color.WHITE else theme.keyText)
                setPadding(dp(9), dp(4), dp(9), dp(4))
                background = roundedBg(
                    if (active) theme.accentColor else theme.keyBg,
                    theme.borderColor,
                    6
                )
                val lp = LinearLayout.LayoutParams(
                    ViewGroup.LayoutParams.WRAP_CONTENT,
                    ViewGroup.LayoutParams.WRAP_CONTENT
                )
                lp.setMargins(0, 0, dp(5), 0)
                layoutParams = lp
                setOnClickListener {
                    playKeyFeedback()
                    selectedLangPair = code
                    renderFullKeyboardUI()
                }
            }
            langRow.addView(chip)
        }

        // Button to grab text from current chat input field into Translate Buffer
        val pullChatBtn = TextView(this).apply {
            text = "📥 Ambil Teks Chat"
            setTextSize(TypedValue.COMPLEX_UNIT_SP, 11f)
            setTypeface(null, Typeface.BOLD)
            setTextColor(Color.WHITE)
            setPadding(dp(9), dp(4), dp(9), dp(4))
            background = roundedBg(Color.parseColor("#059669"), theme.borderColor, 6)
            setOnClickListener {
                playKeyFeedback()
                val extracted = currentInputConnection?.getExtractedText(ExtractedTextRequest(), 0)?.text?.toString()
                    ?: currentInputConnection?.getTextBeforeCursor(200, 0)?.toString()
                    ?: ""
                if (extracted.isNotBlank()) {
                    translateBuffer.clear()
                    translateBuffer.append(extracted.trim())
                    isTypingToTranslateBar = true
                    updateTranslateBufferView()
                } else {
                    Toast.makeText(this@SmartKeyboardService, "Kolom chat masih kosong", Toast.LENGTH_SHORT).show()
                }
            }
        }
        langRow.addView(pullChatBtn)
        langScroll.addView(langRow)
        container.addView(langScroll)

        // Row 2: Interactive Translate Input Box + Translate & Commit Button
        val inputRow = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
            val lp = LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.WRAP_CONTENT
            )
            lp.topMargin = dp(6)
            layoutParams = lp
        }

        val bufferBox = TextView(this).apply {
            text = if (translateBuffer.isEmpty()) {
                "Ketik teks dengan keyboard di bawah untuk diterjemahkan..."
            } else {
                translateBuffer.toString() + "▎"
            }
            setTextSize(TypedValue.COMPLEX_UNIT_SP, 12.5f)
            setTextColor(if (translateBuffer.isEmpty()) theme.mutedText else theme.keyText)
            setPadding(dp(10), dp(8), dp(10), dp(8))
            background = roundedBg(
                theme.boardBg,
                if (isTypingToTranslateBar) theme.accentColor else theme.borderColor,
                8
            )
            layoutParams = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
            setOnClickListener {
                isTypingToTranslateBar = true
                updateTranslateBufferView()
            }
        }
        translateInputDisplay = bufferBox
        inputRow.addView(bufferBox)

        // Clear buffer button
        val clearBtn = TextView(this).apply {
            text = "✕"
            setTextSize(TypedValue.COMPLEX_UNIT_SP, 13f)
            setTypeface(null, Typeface.BOLD)
            setTextColor(theme.mutedText)
            setPadding(dp(8), dp(7), dp(8), dp(7))
            setOnClickListener {
                playKeyFeedback()
                translateBuffer.clear()
                updateTranslateBufferView()
            }
        }
        inputRow.addView(clearBtn)

        // Translate & Commit button
        val goBtn = TextView(this).apply {
            text = if (isTranslating) "⏳..." else "Terjemah ➔"
            setTextSize(TypedValue.COMPLEX_UNIT_SP, 12f)
            setTypeface(null, Typeface.BOLD)
            setTextColor(Color.WHITE)
            setPadding(dp(11), dp(8), dp(11), dp(8))
            background = roundedBg(theme.accentColor, theme.accentColor, 8)
            setOnClickListener {
                playKeyFeedback()
                executeLiveTranslation()
            }
        }
        translateStatusText = goBtn
        inputRow.addView(goBtn)

        container.addView(inputRow)
        return container
    }

    private fun updateTranslateBufferView() {
        val theme = themes[themeIndex]
        translateInputDisplay?.text = if (translateBuffer.isEmpty()) {
            "Ketik teks dengan keyboard di bawah untuk diterjemahkan..."
        } else {
            translateBuffer.toString() + "▎"
        }
        translateInputDisplay?.setTextColor(
            if (translateBuffer.isEmpty()) theme.mutedText else theme.keyText
        )
    }

    private fun executeLiveTranslation() {
        if (isTranslating) return
        val sourceText = if (translateBuffer.isNotBlank()) {
            translateBuffer.toString().trim()
        } else {
            currentInputConnection?.getTextBeforeCursor(250, 0)?.toString()?.trim() ?: ""
        }

        if (sourceText.isEmpty()) {
            Toast.makeText(this, "Ketik kalimat dulu di bar terjemah!", Toast.LENGTH_SHORT).show()
            return
        }

        isTranslating = true
        translateStatusText?.text = "⏳..."

        val langPair = selectedLangPair
        ioExecutor.execute {
            var translatedResult: String? = null
            try {
                val encodedQ = URLEncoder.encode(sourceText, "UTF-8")
                val encodedPair = URLEncoder.encode(langPair, "UTF-8")
                val apiUrl = "https://api.mymemory.translated.net/get?q=$encodedQ&langpair=$encodedPair"
                val conn = (URL(apiUrl).openConnection() as HttpURLConnection).apply {
                    requestMethod = "GET"
                    connectTimeout = 7000
                    readTimeout = 7000
                }
                if (conn.responseCode == 200) {
                    val reader = BufferedReader(InputStreamReader(conn.inputStream))
                    val responseStr = reader.readText()
                    reader.close()
                    val json = JSONObject(responseStr)
                    val respData = json.optJSONObject("responseData")
                    translatedResult = respData?.optString("translatedText")
                }
                conn.disconnect()
            } catch (_: Exception) {
                translatedResult = null
            }

            uiHandler.post {
                isTranslating = false
                translateStatusText?.text = "Terjemah ➔"
                if (!translatedResult.isNullOrBlank()) {
                    // If user had empty buffer and translated directly from chat, replace chat text
                    if (translateBuffer.isEmpty()) {
                        currentInputConnection?.deleteSurroundingText(sourceText.length, 0)
                    }
                    currentInputConnection?.commitText("$translatedResult ", 1)
                    translateBuffer.clear()
                    updateTranslateBufferView()
                } else {
                    Toast.makeText(
                        this@SmartKeyboardService,
                        "Gagal terhubung ke server terjemah. Cek koneksi internet.",
                        Toast.LENGTH_SHORT
                    ).show()
                }
            }
        }
    }

    // =========================================================================
    // FEATURE 2: SMART CLIPBOARD MANAGER PANEL
    // =========================================================================
    private fun buildClipboardPanel(theme: KeyboardTheme): View {
        val panelHeight = getKeyboardHeightPx()
        val container = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, panelHeight)
            setPadding(dp(8), dp(6), dp(8), dp(6))
        }

        // Header Action Row
        val header = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
            setPadding(0, 0, 0, dp(6))
        }

        val title = TextView(this).apply {
            text = "📋 Papan Klip Otomatis (Klik untuk Tempel)"
            setTextSize(TypedValue.COMPLEX_UNIT_SP, 12f)
            setTypeface(null, Typeface.BOLD)
            setTextColor(theme.keyText)
            layoutParams = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
        }
        header.addView(title)

        // Save current chat text to clipboard button
        val addFromChatBtn = TextView(this).apply {
            text = "+ Simpan Teks Chat"
            setTextSize(TypedValue.COMPLEX_UNIT_SP, 11f)
            setTypeface(null, Typeface.BOLD)
            setTextColor(Color.WHITE)
            setPadding(dp(8), dp(4), dp(8), dp(4))
            background = roundedBg(theme.accentColor, theme.accentColor, 6)
            setOnClickListener {
                playKeyFeedback()
                val chatText = currentInputConnection?.getExtractedText(ExtractedTextRequest(), 0)?.text?.toString()
                    ?: currentInputConnection?.getTextBeforeCursor(300, 0)?.toString()
                    ?: ""
                if (chatText.isNotBlank()) {
                    addClipEntry(chatText.trim())
                    Toast.makeText(this@SmartKeyboardService, "Teks disimpan ke Papan Klip!", Toast.LENGTH_SHORT).show()
                } else {
                    Toast.makeText(this@SmartKeyboardService, "Ketik sesuatu di chat lalu klik tombol ini", Toast.LENGTH_SHORT).show()
                }
            }
        }
        header.addView(addFromChatBtn)

        val clearUnpinnedBtn = TextView(this).apply {
            text = "🗑️ Bersihkan"
            setTextSize(TypedValue.COMPLEX_UNIT_SP, 11f)
            setTypeface(null, Typeface.BOLD)
            setTextColor(Color.WHITE)
            setPadding(dp(8), dp(4), dp(8), dp(4))
            background = roundedBg(Color.parseColor("#DC2626"), theme.borderColor, 6)
            val lp = LinearLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT)
            lp.leftMargin = dp(6)
            layoutParams = lp
            setOnClickListener {
                playKeyFeedback()
                clipList.removeAll { !it.pinned }
                saveClipsToPrefs()
                renderFullKeyboardUI()
            }
        }
        header.addView(clearUnpinnedBtn)
        container.addView(header)

        // Scrollable Clip Items
        val scroll = ScrollView(this).apply {
            layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f)
        }
        val listLayout = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
        }

        clipList.forEachIndexed { idx, clip ->
            val card = LinearLayout(this).apply {
                orientation = LinearLayout.HORIZONTAL
                gravity = Gravity.CENTER_VERTICAL
                setPadding(dp(10), dp(8), dp(10), dp(8))
                background = roundedBg(
                    theme.keyBg,
                    if (clip.pinned) theme.accentColor else theme.borderColor,
                    8
                )
                val lp = LinearLayout.LayoutParams(
                    ViewGroup.LayoutParams.MATCH_PARENT,
                    ViewGroup.LayoutParams.WRAP_CONTENT
                )
                lp.bottomMargin = dp(6)
                layoutParams = lp
                setOnClickListener {
                    playKeyFeedback()
                    currentInputConnection?.commitText(clip.text, 1)
                }
            }

            val textCol = LinearLayout(this).apply {
                orientation = LinearLayout.VERTICAL
                layoutParams = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
            }

            val contentTv = TextView(this).apply {
                text = clip.text
                maxLines = 2
                ellipsize = TextUtils.TruncateAt.END
                setTextSize(TypedValue.COMPLEX_UNIT_SP, 12.5f)
                setTextColor(theme.keyText)
            }
            val metaTv = TextView(this).apply {
                text = if (clip.pinned) "📌 Disematkan • ${clip.time}" else "🕒 ${clip.time} • Ketuk untuk Tempel"
                setTextSize(TypedValue.COMPLEX_UNIT_SP, 10f)
                setTextColor(if (clip.pinned) theme.accentColor else theme.mutedText)
            }
            textCol.addView(contentTv)
            textCol.addView(metaTv)
            card.addView(textCol)

            // Pin button
            val pinBtn = TextView(this).apply {
                text = if (clip.pinned) "📌" else "📍"
                setTextSize(TypedValue.COMPLEX_UNIT_SP, 14f)
                setPadding(dp(8), dp(4), dp(8), dp(4))
                setOnClickListener {
                    playKeyFeedback()
                    clip.pinned = !clip.pinned
                    clipList.sortByDescending { it.pinned }
                    saveClipsToPrefs()
                    renderFullKeyboardUI()
                }
            }
            card.addView(pinBtn)

            // Delete single clip button
            val delBtn = TextView(this).apply {
                text = "✕"
                setTextSize(TypedValue.COMPLEX_UNIT_SP, 13f)
                setTextColor(theme.mutedText)
                setPadding(dp(8), dp(4), dp(4), dp(4))
                setOnClickListener {
                    playKeyFeedback()
                    clipList.removeAt(idx)
                    saveClipsToPrefs()
                    renderFullKeyboardUI()
                }
            }
            card.addView(delBtn)

            listLayout.addView(card)
        }

        scroll.addView(listLayout)
        container.addView(scroll)
        return container
    }

    // =========================================================================
    // FEATURE 3: AUTO-TEXT / FAST TEMPLATES PANEL
    // =========================================================================
    private fun buildAutoTextPanel(theme: KeyboardTheme): View {
        val panelHeight = getKeyboardHeightPx()
        val container = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, panelHeight)
            setPadding(dp(8), dp(6), dp(8), dp(6))
        }

        val topRow = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
            setPadding(0, 0, 0, dp(6))
        }

        val headerTv = TextView(this).apply {
            text = "⚡ Template Auto-Text Cepat (1-Klik Kirim)"
            setTextSize(TypedValue.COMPLEX_UNIT_SP, 12f)
            setTypeface(null, Typeface.BOLD)
            setTextColor(theme.keyText)
            layoutParams = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
        }
        topRow.addView(headerTv)

        val saveCurrentAsTemplateBtn = TextView(this).apply {
            text = "+ Simpan Ketikan Chat Jadi Template"
            setTextSize(TypedValue.COMPLEX_UNIT_SP, 11f)
            setTypeface(null, Typeface.BOLD)
            setTextColor(Color.WHITE)
            setPadding(dp(9), dp(5), dp(9), dp(5))
            background = roundedBg(theme.accentColor, theme.accentColor, 6)
            setOnClickListener {
                playKeyFeedback()
                val currentChat = currentInputConnection?.getExtractedText(ExtractedTextRequest(), 0)?.text?.toString()
                    ?: currentInputConnection?.getTextBeforeCursor(300, 0)?.toString()
                    ?: ""
                if (currentChat.isNotBlank()) {
                    autoTextList.add(0, currentChat.trim())
                    saveAutoTextToPrefs()
                    renderFullKeyboardUI()
                    Toast.makeText(this@SmartKeyboardService, "Ditambahkan ke Auto-Text!", Toast.LENGTH_SHORT).show()
                } else {
                    Toast.makeText(this@SmartKeyboardService, "Ketik kalimat di chat dulu untuk disimpan!", Toast.LENGTH_SHORT).show()
                }
            }
        }
        topRow.addView(saveCurrentAsTemplateBtn)
        container.addView(topRow)

        val scroll = ScrollView(this).apply {
            layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f)
        }
        val list = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
        }

        autoTextList.forEachIndexed { index, template ->
            val row = LinearLayout(this).apply {
                orientation = LinearLayout.HORIZONTAL
                gravity = Gravity.CENTER_VERTICAL
                setPadding(dp(10), dp(9), dp(10), dp(9))
                background = roundedBg(theme.keyBg, theme.borderColor, 8)
                val lp = LinearLayout.LayoutParams(
                    ViewGroup.LayoutParams.MATCH_PARENT,
                    ViewGroup.LayoutParams.WRAP_CONTENT
                )
                lp.bottomMargin = dp(6)
                layoutParams = lp
                setOnClickListener {
                    playKeyFeedback()
                    currentInputConnection?.commitText(template, 1)
                }
            }

            val tv = TextView(this).apply {
                text = template
                setTextSize(TypedValue.COMPLEX_UNIT_SP, 12.5f)
                setTextColor(theme.keyText)
                layoutParams = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
            }
            row.addView(tv)

            val del = TextView(this).apply {
                text = "✕"
                setTextSize(TypedValue.COMPLEX_UNIT_SP, 13f)
                setTextColor(theme.mutedText)
                setPadding(dp(8), dp(2), dp(4), dp(2))
                setOnClickListener {
                    playKeyFeedback()
                    autoTextList.removeAt(index)
                    saveAutoTextToPrefs()
                    renderFullKeyboardUI()
                }
            }
            row.addView(del)
            list.addView(row)
        }

        scroll.addView(list)
        container.addView(scroll)
        return container
    }

    // =========================================================================
    // FEATURE 4: BUILT-IN MINI CALCULATOR KEYBOARD
    // =========================================================================
    private fun buildCalculatorPanel(theme: KeyboardTheme): View {
        val panelHeight = getKeyboardHeightPx()
        val container = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, panelHeight)
            setPadding(dp(8), dp(6), dp(8), dp(6))
        }

        // Display bar
        val displayRow = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
            background = roundedBg(theme.specialKeyBg, theme.borderColor, 8)
            setPadding(dp(10), dp(6), dp(10), dp(6))
            val lp = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dp(46))
            lp.bottomMargin = dp(6)
            layoutParams = lp
        }

        val exprTv = TextView(this).apply {
            text = if (calcExpression.isEmpty()) "0" else "${calcExpression} = $calcResultPreview"
            setTextSize(TypedValue.COMPLEX_UNIT_SP, 15f)
            setTypeface(Typeface.MONOSPACE, Typeface.BOLD)
            setTextColor(theme.keyText)
            layoutParams = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
        }
        displayRow.addView(exprTv)

        val sendResultBtn = TextView(this).apply {
            text = "Ketik Hasil ($calcResultPreview) ➔"
            setTextSize(TypedValue.COMPLEX_UNIT_SP, 11.5f)
            setTypeface(null, Typeface.BOLD)
            setTextColor(Color.WHITE)
            setPadding(dp(10), dp(6), dp(10), dp(6))
            background = roundedBg(theme.accentColor, theme.accentColor, 6)
            setOnClickListener {
                playKeyFeedback()
                currentInputConnection?.commitText(calcResultPreview, 1)
            }
        }
        displayRow.addView(sendResultBtn)
        container.addView(displayRow)

        val rows = listOf(
            listOf("7", "8", "9", "÷", "C"),
            listOf("4", "5", "6", "×", "("),
            listOf("1", "2", "3", "-", ")"),
            listOf("0", "000", ".", "+", "=")
        )

        rows.forEach { r ->
            val rowLayout = LinearLayout(this).apply {
                orientation = LinearLayout.HORIZONTAL
                layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f)
            }
            r.forEach { token ->
                val isAccent = token in listOf("=", "C", "÷", "×", "-", "+")
                val btn = TextView(this).apply {
                    text = token
                    gravity = Gravity.CENTER
                    setTextSize(TypedValue.COMPLEX_UNIT_SP, 15f)
                    setTypeface(null, Typeface.BOLD)
                    setTextColor(if (token == "=") Color.WHITE else theme.keyText)
                    background = roundedBg(
                        when (token) {
                            "=" -> theme.accentColor
                            "C" -> Color.parseColor("#DC2626")
                            else -> if (isAccent) theme.specialKeyBg else theme.keyBg
                        },
                        theme.borderColor,
                        8
                    )
                    val lp = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.MATCH_PARENT, 1f)
                    lp.setMargins(dp(3), dp(2), dp(3), dp(2))
                    layoutParams = lp
                    setOnClickListener {
                        playKeyFeedback()
                        when (token) {
                            "C" -> {
                                calcExpression.clear()
                                calcResultPreview = "0"
                            }
                            "=" -> {
                                calcExpression.clear()
                                calcExpression.append(calcResultPreview)
                            }
                            else -> {
                                calcExpression.append(token)
                                calcResultPreview = evaluateCalculator(calcExpression.toString())
                            }
                        }
                        renderFullKeyboardUI()
                    }
                }
                rowLayout.addView(btn)
            }
            container.addView(rowLayout)
        }

        return container
    }

    private fun evaluateCalculator(rawExpr: String): String {
        return try {
            val clean = rawExpr.replace("×", "*").replace("÷", "/").trim()
            val value = object {
                var pos = -1
                var ch = 0
                fun nextChar() {
                    ch = if (++pos < clean.length) clean[pos].code else -1
                }
                fun eat(charToEat: Int): Boolean {
                    while (ch == ' '.code) nextChar()
                    if (ch == charToEat) {
                        nextChar()
                        return true
                    }
                    return false
                }
                fun parse(): Double {
                    nextChar()
                    val x = parseExpression()
                    return x
                }
                fun parseExpression(): Double {
                    var x = parseTerm()
                    while (true) {
                        when {
                            eat('+'.code) -> x += parseTerm()
                            eat('-'.code) -> x -= parseTerm()
                            else -> return x
                        }
                    }
                }
                fun parseTerm(): Double {
                    var x = parseFactor()
                    while (true) {
                        when {
                            eat('*'.code) -> x *= parseFactor()
                            eat('/'.code) -> {
                                val d = parseFactor()
                                x = if (d != 0.0) x / d else 0.0
                            }
                            else -> return x
                        }
                    }
                }
                fun parseFactor(): Double {
                    if (eat('+'.code)) return parseFactor()
                    if (eat('-'.code)) return -parseFactor()
                    var x = 0.0
                    val startPos = pos
                    if (eat('('.code)) {
                        x = parseExpression()
                        eat(')'.code)
                    } else if ((ch in '0'.code..'9'.code) || ch == '.'.code) {
                        while ((ch in '0'.code..'9'.code) || ch == '.'.code) nextChar()
                        x = clean.substring(startPos, pos).toDoubleOrNull() ?: 0.0
                    }
                    return x
                }
            }.parse()

            if (value == value.toLong().toDouble()) {
                value.toLong().toString()
            } else {
                String.format(Locale.US, "%.2f", value)
            }
        } catch (_: Exception) {
            calcResultPreview
        }
    }

    // =========================================================================
    // FEATURE 5: EMOJI, KAOMOJI & SYMBOLS PANEL
    // =========================================================================
    private fun buildEmojiPanel(theme: KeyboardTheme): View {
        val panelHeight = getKeyboardHeightPx()
        val container = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, panelHeight)
            setPadding(dp(8), dp(6), dp(8), dp(6))
        }

        // Sub-tabs
        val tabRow = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            val lp = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dp(34))
            lp.bottomMargin = dp(6)
            layoutParams = lp
        }

        val subTabs = listOf("😀 Emoji Populer", "(≧▽≦) Kaomoji Jepang", "★ Simbol Unik")
        subTabs.forEachIndexed { idx, label ->
            val selected = emojiSubTab == idx
            val tabBtn = TextView(this).apply {
                text = label
                gravity = Gravity.CENTER
                setTextSize(TypedValue.COMPLEX_UNIT_SP, 11.5f)
                setTypeface(null, Typeface.BOLD)
                setTextColor(if (selected) Color.WHITE else theme.keyText)
                background = roundedBg(if (selected) theme.accentColor else theme.keyBg, theme.borderColor, 6)
                val lp = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.MATCH_PARENT, 1f)
                lp.setMargins(dp(2), 0, dp(2), 0)
                layoutParams = lp
                setOnClickListener {
                    playKeyFeedback()
                    emojiSubTab = idx
                    renderFullKeyboardUI()
                }
            }
            tabRow.addView(tabBtn)
        }
        container.addView(tabRow)

        val scroll = ScrollView(this).apply {
            layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f)
        }
        val gridWrapper = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
        }

        val items = when (emojiSubTab) {
            0 -> listOf(
                "😀", "😂", "🤣", "😊", "😍", "🥰", "😎", "🤩",
                "😭", "😤", "😡", "🤔", "🫡", "🙏", "👍", "👏",
                "🔥", "✨", "❤️", "💯", "🎉", "✅", "❌", "⚡",
                "🚀", "💰", "💎", "🛒", "📦", "📱", "💻", "⭐"
            )
            1 -> listOf(
                "(≧▽≦)", "¯\\_(ツ)_/¯", "(╯°□°）╯︵ ┻━┻", "(づ｡◕‿‿◕｡)づ",
                "(•_•) ( •_•)>⌐■-■ (⌐■_■)", "(ಥ﹏ಥ)", "ʕ•ᴥ•ʔ", "(¬‿¬)",
                "(☞ﾟヮﾟ)☞", "☜(ﾟヮﾟ☜)", "(ﾉ◕ヮ◕)ﾉ*:･ﾟ✧", "(っ˘ڡ˘ς)"
            )
            else -> listOf(
                "Rp", "✓", "✗", "★", "☆", "•", "◆", "▶",
                "➔", "⇄", "↑", "↓", "±", "×", "÷", "∞",
                "≈", "≠", "≤", "≥", "©", "®", "™", "§"
            )
        }

        val columns = if (emojiSubTab == 1) 3 else 8
        val chunked = items.chunked(columns)
        chunked.forEach { rowItems ->
            val rLayout = LinearLayout(this).apply {
                orientation = LinearLayout.HORIZONTAL
            }
            rowItems.forEach { item ->
                val cell = TextView(this).apply {
                    text = item
                    gravity = Gravity.CENTER
                    setTextSize(TypedValue.COMPLEX_UNIT_SP, if (emojiSubTab == 0) 20f else 12.5f)
                    setTextColor(theme.keyText)
                    setPadding(dp(4), dp(8), dp(4), dp(8))
                    background = roundedBg(theme.keyBg, theme.borderColor, 7)
                    val lp = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
                    lp.setMargins(dp(2), dp(2), dp(2), dp(2))
                    layoutParams = lp
                    setOnClickListener {
                        playKeyFeedback()
                        commitSmartText(item)
                    }
                }
                rLayout.addView(cell)
            }
            gridWrapper.addView(rLayout)
        }

        scroll.addView(gridWrapper)
        container.addView(scroll)
        return container
    }

    // =========================================================================
    // FEATURE 6: THEMES, KEYBOARD HEIGHT & SOUND/VIBRATION PANEL
    // =========================================================================
    private fun buildThemeSettingsPanel(theme: KeyboardTheme): View {
        val panelHeight = getKeyboardHeightPx()
        val scroll = ScrollView(this).apply {
            layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, panelHeight)
        }
        val container = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(dp(10), dp(8), dp(10), dp(8))
        }

        // 1. Theme selector
        val tLabel = TextView(this).apply {
            text = "🎨 Pilih Tema Keyboard:"
            setTextSize(TypedValue.COMPLEX_UNIT_SP, 12f)
            setTypeface(null, Typeface.BOLD)
            setTextColor(theme.keyText)
        }
        container.addView(tLabel)

        val themeRow = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            val lp = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT)
            lp.topMargin = dp(5)
            lp.bottomMargin = dp(10)
            layoutParams = lp
        }

        themes.forEachIndexed { idx, t ->
            val active = themeIndex == idx
            val btn = TextView(this).apply {
                text = t.name
                gravity = Gravity.CENTER
                setTextSize(TypedValue.COMPLEX_UNIT_SP, 11f)
                setTypeface(null, Typeface.BOLD)
                setTextColor(if (active) Color.WHITE else theme.keyText)
                setPadding(dp(6), dp(8), dp(6), dp(8))
                background = roundedBg(if (active) theme.accentColor else theme.keyBg, theme.borderColor, 7)
                val lp = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
                lp.setMargins(dp(2), 0, dp(2), 0)
                layoutParams = lp
                setOnClickListener {
                    themeIndex = idx
                    prefs.edit().putInt(KEY_THEME, idx).apply()
                    playKeyFeedback()
                    renderFullKeyboardUI()
                }
            }
            themeRow.addView(btn)
        }
        container.addView(themeRow)

        // 2. Height & Sound Controls
        val hLabel = TextView(this).apply {
            text = "📏 Tinggi Keyboard & Efek Suara Ketikan:"
            setTextSize(TypedValue.COMPLEX_UNIT_SP, 12f)
            setTypeface(null, Typeface.BOLD)
            setTextColor(theme.keyText)
        }
        container.addView(hLabel)

        val heightRow = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            val lp = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT)
            lp.topMargin = dp(5)
            lp.bottomMargin = dp(8)
            layoutParams = lp
        }

        listOf("Pendek", "Normal", "Tinggi").forEachIndexed { idx, label ->
            val active = heightIndex == idx
            val btn = TextView(this).apply {
                text = label
                gravity = Gravity.CENTER
                setTextSize(TypedValue.COMPLEX_UNIT_SP, 11f)
                setTypeface(null, Typeface.BOLD)
                setTextColor(if (active) Color.WHITE else theme.keyText)
                setPadding(dp(8), dp(7), dp(8), dp(7))
                background = roundedBg(if (active) theme.accentColor else theme.keyBg, theme.borderColor, 7)
                val lp = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
                lp.setMargins(dp(2), 0, dp(2), 0)
                layoutParams = lp
                setOnClickListener {
                    heightIndex = idx
                    prefs.edit().putInt(KEY_HEIGHT, idx).apply()
                    playKeyFeedback()
                    renderFullKeyboardUI()
                }
            }
            heightRow.addView(btn)
        }
        container.addView(heightRow)

        // Sound & Vibration row
        val soundRow = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            val lp = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT)
            lp.topMargin = dp(2)
            layoutParams = lp
        }

        listOf("🔊 Mech Click", "🫧 Bubble Pop", "🔇 Silent").forEachIndexed { idx, sName ->
            val active = soundMode == idx
            val btn = TextView(this).apply {
                text = sName
                gravity = Gravity.CENTER
                setTextSize(TypedValue.COMPLEX_UNIT_SP, 11f)
                setTypeface(null, Typeface.BOLD)
                setTextColor(if (active) Color.WHITE else theme.keyText)
                setPadding(dp(6), dp(7), dp(6), dp(7))
                background = roundedBg(if (active) theme.accentColor else theme.keyBg, theme.borderColor, 7)
                val lp = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
                lp.setMargins(dp(2), 0, dp(2), 0)
                layoutParams = lp
                setOnClickListener {
                    soundMode = idx
                    prefs.edit().putInt(KEY_SOUND, idx).apply()
                    playKeyFeedback()
                    renderFullKeyboardUI()
                }
            }
            soundRow.addView(btn)
        }

        val vibBtn = TextView(this).apply {
            text = if (vibrateEnabled) "📳 Getar ON" else "📴 Getar OFF"
            gravity = Gravity.CENTER
            setTextSize(TypedValue.COMPLEX_UNIT_SP, 11f)
            setTypeface(null, Typeface.BOLD)
            setTextColor(if (vibrateEnabled) Color.WHITE else theme.keyText)
            setPadding(dp(6), dp(7), dp(6), dp(7))
            background = roundedBg(if (vibrateEnabled) Color.parseColor("#059669") else theme.keyBg, theme.borderColor, 7)
            val lp = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
            lp.setMargins(dp(2), 0, dp(2), 0)
            layoutParams = lp
            setOnClickListener {
                vibrateEnabled = !vibrateEnabled
                prefs.edit().putBoolean(KEY_VIBRATE, vibrateEnabled).apply()
                playKeyFeedback()
                renderFullKeyboardUI()
            }
        }
        soundRow.addView(vibBtn)
        container.addView(soundRow)

        scroll.addView(container)
        return scroll
    }

    // =========================================================================
    // MAIN QWERTY + NUMBER ROW + SPACEBAR TRACKPAD KEYBOARD
    // =========================================================================
    private fun buildQwertyKeyboardArea(theme: KeyboardTheme): View {
        val totalHeight = getKeyboardHeightPx()
        val wrapper = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, totalHeight)
            setPadding(dp(4), dp(4), dp(4), dp(6))
        }

        val numberRow = listOf("1", "2", "3", "4", "5", "6", "7", "8", "9", "0")
        val row1 = if (isSymbolLayer) {
            listOf("@", "#", "Rp", "%", "&", "-", "+", "(", ")", "/")
        } else {
            listOf("q", "w", "e", "r", "t", "y", "u", "i", "o", "p")
        }
        val row2 = if (isSymbolLayer) {
            listOf("*", "\"", "'", ":", ";", "!", "?", "_", "=", "\\")
        } else {
            listOf("a", "s", "d", "f", "g", "h", "j", "k", "l")
        }
        val row3 = if (isSymbolLayer) {
            listOf("~", "`", "|", "•", "√", "π", "÷", "×", "{", "}")
        } else {
            listOf("z", "x", "c", "v", "b", "n", "m")
        }

        // Row 0: Numbers 1-0
        wrapper.addView(buildCharacterRow(numberRow, theme, 0.9f))

        // Row 1: Top Letters / Symbols
        wrapper.addView(buildCharacterRow(row1, theme, 1f))

        // Row 2: Home Row
        wrapper.addView(buildCharacterRow(row2, theme, 1f, horizontalPadDp = if (isSymbolLayer) 0 else 14))

        // Row 3: Shift + Z-M + Backspace (with continuous hold-delete)
        val r3Layout = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f)
        }

        val shiftBtn = TextView(this).apply {
            text = when {
                isSymbolLayer -> "ABC"
                isCapsLock -> "⏫"
                isShiftActive -> "⬆️"
                else -> "⇧"
            }
            gravity = Gravity.CENTER
            setTextSize(TypedValue.COMPLEX_UNIT_SP, 15f)
            setTypeface(null, Typeface.BOLD)
            setTextColor(if (isShiftActive || isCapsLock) Color.WHITE else theme.keyText)
            background = roundedBg(
                if (isShiftActive || isCapsLock) theme.accentColor else theme.specialKeyBg,
                theme.borderColor,
                7
            )
            val lp = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.MATCH_PARENT, 1.45f)
            lp.setMargins(dp(2), dp(3), dp(2), dp(3))
            layoutParams = lp
            setOnClickListener {
                playKeyFeedback()
                if (isSymbolLayer) {
                    isSymbolLayer = false
                } else {
                    val now = System.currentTimeMillis()
                    if (now - lastShiftTapTime < 350L) {
                        isCapsLock = true
                        isShiftActive = true
                    } else if (isCapsLock) {
                        isCapsLock = false
                        isShiftActive = false
                    } else {
                        isShiftActive = !isShiftActive
                    }
                    lastShiftTapTime = now
                }
                renderFullKeyboardUI()
            }
        }
        r3Layout.addView(shiftBtn)

        row3.forEach { rawKey ->
            val displayChar = formatCase(rawKey)
            r3Layout.addView(createCharKeyView(displayChar, theme, 1f))
        }

        // Backspace Button with Hold-to-Repeat
        val backspaceBtn = TextView(this).apply {
            text = "⌫"
            gravity = Gravity.CENTER
            setTextSize(TypedValue.COMPLEX_UNIT_SP, 16f)
            setTypeface(null, Typeface.BOLD)
            setTextColor(theme.keyText)
            background = roundedBg(theme.specialKeyBg, theme.borderColor, 7)
            val lp = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.MATCH_PARENT, 1.45f)
            lp.setMargins(dp(2), dp(3), dp(2), dp(3))
            layoutParams = lp
            setOnTouchListener { v, event ->
                when (event.actionMasked) {
                    MotionEvent.ACTION_DOWN -> {
                        v.alpha = 0.7f
                        isBackspaceHeld = true
                        handleBackspace()
                        playKeyFeedback()
                        uiHandler.postDelayed(backspaceRunnable, 350L)
                        true
                    }
                    MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {
                        v.alpha = 1.0f
                        isBackspaceHeld = false
                        uiHandler.removeCallbacks(backspaceRunnable)
                        true
                    }
                    else -> false
                }
            }
        }
        r3Layout.addView(backspaceBtn)
        wrapper.addView(r3Layout)

        // Row 4: ?123 | Comma | SPACEBAR TRACKPAD | Period | Enter
        val r4Layout = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1.05f)
        }

        val symToggleBtn = TextView(this).apply {
            text = if (isSymbolLayer) "ABC" else "?123"
            gravity = Gravity.CENTER
            setTextSize(TypedValue.COMPLEX_UNIT_SP, 13f)
            setTypeface(null, Typeface.BOLD)
            setTextColor(theme.keyText)
            background = roundedBg(theme.specialKeyBg, theme.borderColor, 7)
            val lp = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.MATCH_PARENT, 1.5f)
            lp.setMargins(dp(2), dp(3), dp(2), dp(3))
            layoutParams = lp
            setOnClickListener {
                playKeyFeedback()
                isSymbolLayer = !isSymbolLayer
                renderFullKeyboardUI()
            }
        }
        r4Layout.addView(symToggleBtn)

        r4Layout.addView(createCharKeyView(",", theme, 1f))

        // SPACEBAR WITH CURSOR TRACKPAD SLIDE
        val spaceBtn = TextView(this).apply {
            text = if (isTypingToTranslateBar && activeTab == "TRANSLATE") {
                "◀ SPASI (KETIK TERJEMAH) ▶"
            } else {
                "◀ GESER SPASI = KURSOR ▶"
            }
            gravity = Gravity.CENTER
            setTextSize(TypedValue.COMPLEX_UNIT_SP, 11f)
            setTypeface(null, Typeface.BOLD)
            setTextColor(theme.mutedText)
            background = roundedBg(theme.keyBg, theme.borderColor, 8)
            val lp = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.MATCH_PARENT, 4.8f)
            lp.setMargins(dp(3), dp(3), dp(3), dp(3))
            layoutParams = lp

            var downX = 0f
            var lastStepX = 0f
            var didSlideCursor = false
            val stepThresholdPx = dp(14).toFloat()

            setOnTouchListener { v, event ->
                when (event.actionMasked) {
                    MotionEvent.ACTION_DOWN -> {
                        v.alpha = 0.75f
                        downX = event.x
                        lastStepX = event.x
                        didSlideCursor = false
                        playKeyFeedback()
                        true
                    }
                    MotionEvent.ACTION_MOVE -> {
                        val deltaFromStep = event.x - lastStepX
                        if (abs(event.x - downX) > stepThresholdPx) {
                            didSlideCursor = true
                        }
                        if (abs(deltaFromStep) >= stepThresholdPx) {
                            val steps = (deltaFromStep / stepThresholdPx).toInt()
                            if (steps != 0) {
                                moveCursorBySteps(steps)
                                lastStepX += steps * stepThresholdPx
                            }
                        }
                        true
                    }
                    MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {
                        v.alpha = 1.0f
                        if (!didSlideCursor) {
                            commitSmartText(" ")
                        }
                        true
                    }
                    else -> false
                }
            }
        }
        r4Layout.addView(spaceBtn)

        r4Layout.addView(createCharKeyView(".", theme, 1f))

        val enterBtn = TextView(this).apply {
            text = if (isTypingToTranslateBar && activeTab == "TRANSLATE") "🌍➔" else "↵"
            gravity = Gravity.CENTER
            setTextSize(TypedValue.COMPLEX_UNIT_SP, 16f)
            setTypeface(null, Typeface.BOLD)
            setTextColor(Color.WHITE)
            background = roundedBg(theme.accentColor, theme.accentColor, 7)
            val lp = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.MATCH_PARENT, 1.6f)
            lp.setMargins(dp(2), dp(3), dp(2), dp(3))
            layoutParams = lp
            setOnClickListener {
                playKeyFeedback()
                if (isTypingToTranslateBar && activeTab == "TRANSLATE") {
                    executeLiveTranslation()
                } else {
                    handleEnterKey()
                }
            }
        }
        r4Layout.addView(enterBtn)

        wrapper.addView(r4Layout)
        return wrapper
    }

    private fun buildCharacterRow(
        keys: List<String>,
        theme: KeyboardTheme,
        weight: Float,
        horizontalPadDp: Int = 0
    ): View {
        val row = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, weight)
            if (horizontalPadDp > 0) {
                setPadding(dp(horizontalPadDp), 0, dp(horizontalPadDp), 0)
            }
        }
        keys.forEach { k ->
            val charStr = formatCase(k)
            row.addView(createCharKeyView(charStr, theme, 1f))
        }
        return row
    }

    private fun createCharKeyView(label: String, theme: KeyboardTheme, weight: Float): View {
        return TextView(this).apply {
            text = label
            gravity = Gravity.CENTER
            setTextSize(TypedValue.COMPLEX_UNIT_SP, 15.5f)
            setTypeface(null, Typeface.BOLD)
            setTextColor(theme.keyText)
            background = roundedBg(theme.keyBg, theme.borderColor, 7)
            val lp = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.MATCH_PARENT, weight)
            lp.setMargins(dp(2), dp(3), dp(2), dp(3))
            layoutParams = lp

            setOnTouchListener { v, event ->
                when (event.actionMasked) {
                    MotionEvent.ACTION_DOWN -> {
                        v.scaleX = 1.08f
                        v.scaleY = 1.08f
                        keyPreviewBanner?.text = label
                        playKeyFeedback()
                        true
                    }
                    MotionEvent.ACTION_UP -> {
                        v.scaleX = 1.0f
                        v.scaleY = 1.0f
                        commitSmartText(label)
                        if (isShiftActive && !isCapsLock) {
                            isShiftActive = false
                            renderFullKeyboardUI()
                        }
                        true
                    }
                    MotionEvent.ACTION_CANCEL -> {
                        v.scaleX = 1.0f
                        v.scaleY = 1.0f
                        true
                    }
                    else -> false
                }
            }
        }
    }

    private fun formatCase(raw: String): String {
        if (isSymbolLayer) return raw
        return if (isShiftActive || isCapsLock) raw.uppercase(Locale.getDefault()) else raw.lowercase(Locale.getDefault())
    }

    private fun commitSmartText(text: String) {
        if (activeTab == "TRANSLATE" && isTypingToTranslateBar) {
            translateBuffer.append(text)
            updateTranslateBufferView()
        } else {
            currentInputConnection?.commitText(text, 1)
        }
    }

    private fun handleBackspace() {
        if (activeTab == "TRANSLATE" && isTypingToTranslateBar && translateBuffer.isNotEmpty()) {
            translateBuffer.deleteCharAt(translateBuffer.length - 1)
            updateTranslateBufferView()
            return
        }
        val ic = currentInputConnection ?: return
        val selected = ic.getSelectedText(0)
        if (!TextUtils.isEmpty(selected)) {
            ic.commitText("", 1)
        } else {
            ic.deleteSurroundingText(1, 0)
        }
    }

    private fun moveCursorBySteps(steps: Int) {
        if (steps == 0) return
        val keyCode = if (steps > 0) KeyEvent.KEYCODE_DPAD_RIGHT else KeyEvent.KEYCODE_DPAD_LEFT
        val count = abs(steps).coerceAtMost(5)
        repeat(count) {
            sendDownUpKeyEvents(keyCode)
        }
    }

    private fun handleEnterKey() {
        val ic = currentInputConnection ?: return
        val info = currentInputEditorInfo
        if (info != null) {
            val imeAction = info.imeOptions and EditorInfo.IME_MASK_ACTION
            val isMultiLine = (info.inputType and InputType.TYPE_TEXT_FLAG_MULTI_LINE) != 0
            if (!isMultiLine && imeAction != EditorInfo.IME_ACTION_NONE && imeAction != EditorInfo.IME_ACTION_UNSPECIFIED) {
                ic.performEditorAction(imeAction)
                return
            }
        }
        ic.commitText("\n", 1)
    }

    // =========================================================================
    // AUDIO & HAPTIC FEEDBACK HELPERS
    // =========================================================================
    private fun playKeyFeedback() {
        if (soundMode != 2) {
            try {
                val tone = if (soundMode == 0) {
                    ToneGenerator.TONE_PROP_BEEP
                } else {
                    ToneGenerator.TONE_PROP_ACK
                }
                toneGenerator?.startTone(tone, 22)
            } catch (_: Exception) {}
        }

        if (vibrateEnabled) {
            try {
                if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
                    vibrator?.vibrate(VibrationEffect.createOneShot(14L, VibrationEffect.DEFAULT_AMPLITUDE))
                } else {
                    @Suppress("DEPRECATION")
                    vibrator?.vibrate(14L)
                }
            } catch (_: Exception) {}
        }
    }

    private fun getKeyboardHeightPx(): Int {
        val dpVal = when (heightIndex) {
            0 -> 215 // Pendek (Compact)
            1 -> 252 // Normal
            else -> 290 // Tinggi (Tall)
        }
        return dp(dpVal)
    }

    private fun roundedBg(fillColor: Int, strokeColor: Int, radiusDp: Int): GradientDrawable {
        return GradientDrawable().apply {
            shape = GradientDrawable.RECTANGLE
            cornerRadius = dp(radiusDp).toFloat()
            setColor(fillColor)
            setStroke(dp(1), strokeColor)
        }
    }

    private fun dp(value: Int): Int {
        return TypedValue.applyDimension(
            TypedValue.COMPLEX_UNIT_DIP,
            value.toFloat(),
            resources.displayMetrics
        ).toInt()
    }
}
