;;; lumber.el --- Log analysis pattern manager -*- lexical-binding: t -*-

;; Author: shuaiy
;; Version: 0.2.0
;; Package-Requires: ((emacs "29.1") (transient "0.6"))
;; Keywords: tools, matching, logs
;; URL: https://github.com/theshuaiyuan/lumber

;;; Commentary:
;; Lumber manages color-coded search patterns for log file analysis.
;; It integrates with occur, vlf-occur, grep, and ripgrep backends,
;; and applies per-pattern colored highlighting in results buffers.

;;; Code:

(require 'cl-lib)
(require 'transient)
(require 'hi-lock)
(require 'tabulated-list)
(require 'compile)

;;;; Customization

(defgroup lumber nil
  "Log analysis pattern manager."
  :group 'tools
  :prefix "lumber-")

(defcustom lumber-persist-file
  (locate-user-emacs-file "lumber-sets.eld")
  "File for persisting saved pattern sets across sessions."
  :type 'file
  :group 'lumber)

(defcustom lumber-default-colors
  '(("white"   . "red")
    ("black"   . "orange")
    ("white"   . "blue")
    ("black"   . "green3")
    ("white"   . "purple")
    ("black"   . "cyan")
    ("white"   . "dark green")
    ("black"   . "yellow"))
  "Default (foreground . background) color pairs, assigned in order."
  :type '(repeat (cons string string))
  :group 'lumber)

(defcustom lumber-search-backend 'auto
  "Default search backend.
- auto:      use vlf-occur if buffer is in vlf-mode, otherwise occur
- occur:     always use occur
- vlf-occur: always use vlf-occur
- grep:      use external grep
- ripgrep:   use external rg"
  :type '(choice (const auto) (const occur) (const vlf-occur)
                 (const grep) (const ripgrep))
  :group 'lumber)

(defcustom lumber-result-window-height 0.3
  "Default height ratio for the results window (0.0 - 1.0)."
  :type 'float
  :group 'lumber)

(defcustom lumber-result-window-height-max 0.85
  "Expanded height ratio for the results window when toggled."
  :type 'float
  :group 'lumber)

(defcustom lumber-context-lines 0
  "Number of context lines around each match (for grep/rg backend)."
  :type 'natnum
  :group 'lumber)

;;;; Internal State

(defvar lumber--patterns nil
  "List of pattern plists.  This is the global active working set.
Highlight state is applied per-buffer on demand via `lumber--apply-highlights';
not every open buffer is automatically kept in sync.")

(defvar lumber--current-set-name nil
  "Name of the currently loaded pattern set, or nil if none.")

(defvar lumber--history nil
  "Minibuffer input history for pattern strings.")

(defvar lumber--face-cache (make-hash-table :test 'equal)
  "Cache of generated faces keyed by (foreground . background).")

(defvar lumber--face-counter 0
  "Counter for auto-incrementing lumber face names.")

(defvar-local lumber--applied-regexps nil
  "Regexps currently highlighted by lumber in this buffer.
Used by `lumber--clear-highlights' to remove exactly what was applied.")

(defvar-local lumber--header-line-remap-cookie nil
  "Cookie from `face-remap-add-relative' for the header-line remap.
Saved so it can be removed when the major mode changes.")

;;;; Face Generation

(defun lumber--get-face (foreground background)
  "Return a face symbol for FOREGROUND and BACKGROUND colors.
Creates and caches the face if it doesn't exist yet."
  (let* ((key (cons foreground background))
         (cached (gethash key lumber--face-cache)))
    (or cached
        (let* ((n (cl-incf lumber--face-counter))
               (face-sym (intern (format "lumber-face-%d" n))))
          (face-spec-set face-sym
                         `((t :foreground ,foreground
                              :background ,background)))
          (puthash key face-sym lumber--face-cache)
          face-sym))))

;;;; Pattern → Regexp Conversion

(defun lumber--expand-case-insensitive (str)
  "Expand alphabetic chars in STR to [Aa] form for case-insensitive matching."
  (mapconcat (lambda (c)
               (cond
                ((and (>= c ?a) (<= c ?z))
                 (format "[%c%c]" (upcase c) c))
                ((and (>= c ?A) (<= c ?Z))
                 (format "[%c%c]" c (downcase c)))
                (t (string c))))
             str ""))

(defun lumber--has-uppercase (str)
  "Return non-nil if STR contains at least one uppercase letter."
  (string-match-p "[A-Z]" str))

(defun lumber--pattern-to-regexp (pattern-plist)
  "Convert PATTERN-PLIST to a regexp string suitable for Emacs searching.
Strategy: run all searches with case-fold-search=nil; apply [Aa]-expansion
to achieve case-insensitivity for literal patterns.

Limitation: :type regexp with :case-sensitive nil/auto is not expanded
(char-class expansion would break regexp syntax). In that case the pattern
is returned as-is and case-sensitivity follows the pattern's own uppercase
presence. For regexp patterns needing true case-insensitivity, prefix the
pattern string with \\(?i:...\\) manually if the regexp engine supports it."
  (let* ((pat    (plist-get pattern-plist :pattern))
         (type   (plist-get pattern-plist :type))
         (case-s (plist-get pattern-plist :case-sensitive))
         (base   (if (eq type 'literal) (regexp-quote pat) pat)))
    (cond
     ;; Explicitly case-sensitive: use as-is
     ((eq case-s t) base)
     ;; Explicitly case-insensitive
     ((eq case-s nil)
      (if (eq type 'literal)
          (lumber--expand-case-insensitive base)
        ;; regexp: cannot safely expand; return as-is
        base))
     ;; Auto: if pattern has uppercase → treat as sensitive, else expand
     (t (if (lumber--has-uppercase pat)
            base
          (if (eq type 'literal)
              (lumber--expand-case-insensitive base)
            base))))))

;;;; Combined Regexp

(defun lumber--build-combined-regexp ()
  "Build a combined regexp from all enabled patterns.
Uses \\| (Emacs regexp syntax) as alternation."
  (let ((enabled (cl-remove-if-not
                  (lambda (p) (plist-get p :enabled))
                  lumber--patterns)))
    (when enabled
      (mapconcat #'lumber--pattern-to-regexp enabled "\\|"))))

(defun lumber--build-grep-regexp ()
  "Build a combined regexp for external tools (grep -E / ripgrep).
Uses | as alternation."
  (let ((enabled (cl-remove-if-not
                  (lambda (p) (plist-get p :enabled))
                  lumber--patterns)))
    (when enabled
      (mapconcat #'lumber--pattern-to-regexp enabled "|"))))

;;;; Highlight Application

(defun lumber--apply-highlights (&optional buffer)
  "Apply per-pattern highlights in BUFFER (default: current buffer).
Reads from the global `lumber--patterns'; applied state is tracked
per-buffer in `lumber--applied-regexps'.  Clears any existing lumber
highlights in BUFFER before re-applying so stale hi-lock state cannot
accumulate on repeated calls."
  (with-current-buffer (or buffer (current-buffer))
    (lumber--clear-highlights)
    (hi-lock-mode 1)
    (dolist (pat lumber--patterns)
      (when (plist-get pat :enabled)
        (let* ((regexp (lumber--pattern-to-regexp pat))
               (fg     (plist-get pat :foreground))
               (bg     (plist-get pat :background))
               (face   (lumber--get-face fg bg)))
          (highlight-regexp regexp face)
          (push regexp lumber--applied-regexps))))))

(defun lumber--clear-highlights (&optional buffer)
  "Remove all lumber-managed highlights in BUFFER (default: current buffer).
Reads from the buffer-local `lumber--applied-regexps' registry rather than
recomputing from the current pattern set, so patterns that have already been
edited or removed are still cleaned up correctly."
  (with-current-buffer (or buffer (current-buffer))
    (dolist (regexp lumber--applied-regexps)
      (ignore-errors
        (unhighlight-regexp regexp)))
    (setq lumber--applied-regexps nil)))

;;;; Color Assignment

(defun lumber--next-color ()
  "Return the next color pair from `lumber-default-colors'.
Color pairs are (foreground . background). Cycles through,
preferring pairs not already in use."
  (let* ((used (mapcar (lambda (p)
                         (cons (plist-get p :foreground)
                               (plist-get p :background)))
                       lumber--patterns))
         (available (cl-remove-if (lambda (c) (member c used))
                                  lumber-default-colors)))
    (if available
        (car available)
      ;; All colors used — cycle by index
      (nth (mod (length lumber--patterns) (length lumber-default-colors))
           lumber-default-colors))))

;;;; Pattern Display Helper

(defun lumber--pattern-display (pat)
  "Return a display string for PAT suitable for completing-read."
  (let ((p (plist-get pat :pattern))
        (fg (plist-get pat :foreground))
        (bg (plist-get pat :background)))
    (propertize (format "%-30s [%s/%s]" p fg bg)
                'face (lumber--get-face fg bg))))

(defun lumber--select-pattern (prompt)
  "Use completing-read with PROMPT to select a pattern from `lumber--patterns'.
Returns the selected pattern plist or nil."
  (when lumber--patterns
    (let* ((choices (mapcar (lambda (p)
                              (cons (lumber--pattern-display p) p))
                            lumber--patterns))
           (sel (completing-read prompt (mapcar #'car choices) nil t)))
      (cdr (assoc sel choices)))))

;;;; List Buffer Helper

(defun lumber--after-patterns-changed ()
  "Reapply lumber highlights in the current buffer and refresh *Lumber Patterns*.
Only the current buffer's highlights are updated; other open buffers where
lumber highlights may already have been applied are not affected."
  (lumber--apply-highlights)
  (lumber--refresh-list-buffer))

(defun lumber--refresh-list-buffer ()
  "Refresh the *Lumber Patterns* buffer if it exists and is in `lumber-list-mode'."
  (when-let ((buf (get-buffer "*Lumber Patterns*")))
    (with-current-buffer buf
      (when (derived-mode-p 'lumber-list-mode)
        (tabulated-list-revert)
        (lumber--add-color-overlays)))))

;;;; CRUD: Add

;;;###autoload
(defun lumber-add (&optional pattern-string)
  "Add a new pattern with full interactive prompts."
  (interactive)
  (let* ((pat (or pattern-string
                  (read-string "Pattern: " nil 'lumber--history)))
         (type-char (read-char-choice "Type [l]iteral/[r]egexp (default l): "
                                      '(?l ?r ?\r)))
         (type (if (eq type-char ?r) 'regexp 'literal))
         (case-char (read-char-choice
                     "Case sensitive [y]es/[n]o/[a]uto (default a): "
                     '(?y ?n ?a ?\r)))
         (case-s (cond ((eq case-char ?y) t)
                       ((eq case-char ?n) nil)
                       (t 'auto)))
         (color (lumber--next-color))
         (fg (car color))
         (bg (cdr color))
         (plist (list :pattern pat
                      :type type
                      :case-sensitive case-s
                      :foreground fg
                      :background bg
                      :enabled t)))
    (setq lumber--patterns (nconc lumber--patterns (list plist)))
    (lumber--after-patterns-changed)
    (message "Added: %s (%s, %s-case, ■ %s/%s) [%d patterns]"
             pat type case-s bg fg (length lumber--patterns))))

;;;###autoload
(defun lumber-quick-add ()
  "Add a pattern using defaults (literal, auto case, next color)."
  (interactive)
  (let* ((pat (read-string "Pattern: " nil 'lumber--history))
         (color (lumber--next-color))
         (fg (car color))
         (bg (cdr color))
         (plist (list :pattern pat
                      :type 'literal
                      :case-sensitive 'auto
                      :foreground fg
                      :background bg
                      :enabled t)))
    (setq lumber--patterns (nconc lumber--patterns (list plist)))
    (lumber--after-patterns-changed)
    (message "Added: %s (literal, auto-case, ■ %s/%s) [%d patterns]"
             pat bg fg (length lumber--patterns))))

;;;; CRUD: Read

;;;###autoload
(defun lumber-list ()
  "Open or refresh the `*Lumber Patterns*' management buffer."
  (interactive)
  (let ((buf (get-buffer-create "*Lumber Patterns*")))
    (with-current-buffer buf
      (unless (derived-mode-p 'lumber-list-mode)
        (lumber-list-mode)))
    (pop-to-buffer buf))
  (lumber--refresh-list-buffer))

;;;###autoload
(defun lumber-list-brief ()
  "Display all patterns in the echo area."
  (interactive)
  (if (null lumber--patterns)
      (message "No patterns defined.")
    (let ((parts (mapcar (lambda (p)
                           (let* ((fg (plist-get p :foreground))
                                  (bg (plist-get p :background))
                                  (face (lumber--get-face fg bg))
                                  (marker (if (plist-get p :enabled) "■" "✗")))
                             (propertize (format "%s %s" marker (plist-get p :pattern))
                                         'face face)))
                         lumber--patterns)))
      (message "%s" (string-join parts " │ ")))))

;;;; CRUD: Edit

;;;###autoload
(defun lumber-edit ()
  "Edit a pattern selected via completing-read."
  (interactive)
  (let ((pat (lumber--select-pattern "Edit pattern: ")))
    (unless pat
      (user-error "No patterns to edit"))
    (lumber--edit-pattern pat)))

(defun lumber--edit-pattern (pat)
  "Interactively edit PAT in place."
  (let* ((old-pat   (plist-get pat :pattern))
         (old-type  (plist-get pat :type))
         (old-case  (plist-get pat :case-sensitive))
         (old-fg    (plist-get pat :foreground))
         (old-bg    (plist-get pat :background))
         (new-pat   (read-string (format "Pattern [%s]: " old-pat)
                                 nil 'lumber--history old-pat))
         (type-char (read-char-choice
                     (format "Type [l]iteral/[r]egexp (current: %s): " old-type)
                     '(?l ?r ?\r)))
         (new-type  (cond ((eq type-char ?l) 'literal)
                          ((eq type-char ?r) 'regexp)
                          (t old-type)))
         (case-char (read-char-choice
                     (format "Case [y]es/[n]o/[a]uto (current: %s): " old-case)
                     '(?y ?n ?a ?\r)))
         (new-case  (cond ((eq case-char ?y) t)
                          ((eq case-char ?n) nil)
                          ((eq case-char ?a) 'auto)
                          (t old-case)))
         (new-fg    (read-string (format "Foreground [%s]: " old-fg)
                                 nil nil old-fg))
         (new-bg    (read-string (format "Background [%s]: " old-bg)
                                 nil nil old-bg)))
    (plist-put pat :pattern new-pat)
    (plist-put pat :type new-type)
    (plist-put pat :case-sensitive new-case)
    (plist-put pat :foreground new-fg)
    (plist-put pat :background new-bg)
    (lumber--after-patterns-changed)
    (message "Updated pattern: %s" new-pat)))

;;;###autoload
(defun lumber-toggle ()
  "Toggle enabled/disabled for a pattern selected via completing-read."
  (interactive)
  (let ((pat (lumber--select-pattern "Toggle pattern: ")))
    (unless pat
      (user-error "No patterns to toggle"))
    (let* ((current (plist-get pat :enabled))
           (new-val (not current)))
      (plist-put pat :enabled new-val)
      (lumber--after-patterns-changed)
      (message "Toggled: %s → %s"
               (plist-get pat :pattern)
               (if new-val "enabled" "disabled")))))

;;;; CRUD: Delete

;;;###autoload
(defun lumber-remove ()
  "Remove a pattern selected via completing-read."
  (interactive)
  (let ((pat (lumber--select-pattern "Remove pattern: ")))
    (unless pat
      (user-error "No patterns to remove"))
    (setq lumber--patterns (delq pat lumber--patterns))
    (lumber--after-patterns-changed)
    (message "Removed: %s [%d remaining]"
             (plist-get pat :pattern)
             (length lumber--patterns))))

;;;###autoload
(defun lumber-clear ()
  "Clear the active pattern set and remove lumber-managed highlights in the current buffer.
Does not retroactively clear highlights in other open buffers where they may
already have been applied."
  (interactive)
  (setq lumber--patterns nil)
  (lumber--after-patterns-changed)
  (message "Cleared all patterns."))

;;;; Search Backends

(defun lumber--resolve-backend ()
  "Resolve the effective backend symbol from `lumber-search-backend'."
  (if (eq lumber-search-backend 'auto)
      (cond
       ((bound-and-true-p vlf-mode) 'vlf-occur)
       ((and (executable-find "rg") buffer-file-name) 'ripgrep)
       (t 'occur))
    lumber-search-backend))

;;;###autoload
(defun lumber-search (&optional backend)
  "Run a search using all enabled patterns.
BACKEND overrides `lumber-search-backend'."
  (interactive)
  (unless lumber--patterns
    (user-error "No patterns defined. Use lumber-add first"))
  (let ((enabled (cl-remove-if-not (lambda (p) (plist-get p :enabled))
                                   lumber--patterns)))
    (unless enabled
      (user-error "No enabled patterns. Use lumber-toggle to enable some"))
    (let ((effective (or backend (lumber--resolve-backend))))
      (pcase effective
        ('occur     (lumber-search-occur))
        ('vlf-occur (lumber-search-vlf-occur))
        ('grep      (lumber-search-grep))
        ('ripgrep   (lumber-search-ripgrep))
        (_ (lumber-search-occur))))))

;;;###autoload
(defun lumber-search-occur ()
  "Search using occur backend with all enabled patterns."
  (interactive)
  (unless lumber--patterns
    (user-error "No patterns defined"))
  (let ((regexp (lumber--build-combined-regexp)))
    (unless regexp
      (user-error "No enabled patterns"))
    (let ((case-fold-search nil))
      (occur regexp))))

;;;###autoload
(defun lumber-search-vlf-occur ()
  "Search using vlf-occur backend."
  (interactive)
  (unless (featurep 'vlf)
    (user-error "vlf package is not loaded"))
  (unless (bound-and-true-p vlf-mode)
    (user-error "Buffer is not in vlf-mode"))
  (let ((regexp (lumber--build-combined-regexp)))
    (unless regexp
      (user-error "No enabled patterns"))
    (let ((case-fold-search nil))
      (vlf-occur regexp))))

;;;###autoload
(defun lumber-search-grep ()
  "Search using external grep backend.
Note: :type regexp patterns are passed as-is to grep -E; Emacs regexp syntax
differs from POSIX ERE, so complex regexp patterns may need adjustment."
  (interactive)
  (unless lumber--patterns
    (user-error "No patterns defined"))
  (let* ((regexp (lumber--build-grep-regexp)))
    (unless regexp
      (user-error "No enabled patterns"))
    (let* ((file (or buffer-file-name
                     (and (boundp 'vlf-file-name) vlf-file-name)
                     (read-file-name "Search file: ")))
           (ctx  lumber-context-lines)
           (cmd  (format "grep -nEH %s %s %s"
                         (if (> ctx 0) (format "-C %d" ctx) "")
                         (shell-quote-argument regexp)
                         (shell-quote-argument (expand-file-name file)))))
      (grep cmd))))

;;;###autoload
(defun lumber-search-ripgrep ()
  "Search using ripgrep backend.
Uses the same [Aa]-expansion strategy as other backends for consistent
case-sensitivity handling, passing a single combined regexp to rg.
Note: :type regexp patterns are passed as-is to rg; some Emacs regexp
constructs are not supported by ripgrep's regexp engine and may need
adjustment."
  (interactive)
  (unless lumber--patterns
    (user-error "No patterns defined"))
  (unless (executable-find "rg")
    (user-error "ripgrep (rg) not found in PATH"))
  (let* ((regexp (lumber--build-grep-regexp)))
    (unless regexp
      (user-error "No enabled patterns"))
    (let* ((file (or buffer-file-name
                     (and (boundp 'vlf-file-name) vlf-file-name)
                     (read-file-name "Search file: ")))
           (ctx-flag (if (> lumber-context-lines 0)
                         (format "-C %d" lumber-context-lines)
                       ""))
           (buf-name (format "*lumber-rg<%s>*"
                             (file-name-nondirectory file)))
           (cmd (format "rg --no-heading -n --color=never --case-sensitive %s -e %s %s"
                        ctx-flag
                        (shell-quote-argument regexp)
                        (shell-quote-argument (expand-file-name file)))))
      (compilation-start cmd 'grep-mode (lambda (_) buf-name)))))

;;;; Apply/Clear Highlights (interactive)

;;;###autoload
(defun lumber-apply-highlights ()
  "Reapply all lumber highlights in the current buffer."
  (interactive)
  (lumber--apply-highlights)
  (message "Highlights applied."))

;;;###autoload
(defun lumber-clear-highlights ()
  "Remove all lumber highlights from the current buffer."
  (interactive)
  (lumber--clear-highlights)
  (message "Highlights cleared."))

;;;; Tabulated-List Management Buffer

(defun lumber--list-entries ()
  "Generate entries for `tabulated-list-mode' from `lumber--patterns'."
  (cl-loop for pat in lumber--patterns
           for i from 0
           collect
           (let* ((enabled (plist-get pat :enabled))
                  (type    (plist-get pat :type))
                  (case-s  (plist-get pat :case-sensitive))
                  (pattern (plist-get pat :pattern))
                  (fg      (plist-get pat :foreground))
                  (bg      (plist-get pat :background))
                  (face    (lumber--get-face fg bg))
                  (status  (propertize (if enabled "✓" "✗")
                                       'face (if enabled
                                                 '(:foreground "green")
                                               '(:foreground "red"))))
                  (type-s  (symbol-name type))
                  (case-s-str (cond ((eq case-s t)    "yes")
                                   ((eq case-s nil)   "no")
                                   (t                 "auto")))
                  (colors  (propertize (format "■ %s/%s" fg bg)
                                       'face face
                                       'font-lock-face face
                                       'rear-nonsticky t
                                       'lumber-colors-cell t)))
             (list i (vector pattern status type-s case-s-str colors)))))

(defun lumber--list-get-pattern ()
  "Return the pattern plist for the entry at point in `lumber-list-mode'."
  (let ((id (tabulated-list-get-id)))
    (when (and id (< id (length lumber--patterns)))
      (nth id lumber--patterns))))

;;;###autoload
(defun lumber-remove-at-point ()
  "Remove the pattern at point in `*Lumber Patterns*'."
  (interactive)
  (let ((pat (lumber--list-get-pattern)))
    (unless pat
      (user-error "No pattern at point"))
    (setq lumber--patterns (delq pat lumber--patterns))
    (lumber--after-patterns-changed)
    (message "Removed: %s [%d remaining]"
             (plist-get pat :pattern) (length lumber--patterns))))

;;;###autoload
(defun lumber-toggle-at-point ()
  "Toggle enabled/disabled for the pattern at point."
  (interactive)
  (let ((pat (lumber--list-get-pattern)))
    (unless pat
      (user-error "No pattern at point"))
    (plist-put pat :enabled (not (plist-get pat :enabled)))
    (lumber--after-patterns-changed)
    (message "Toggled: %s → %s"
             (plist-get pat :pattern)
             (if (plist-get pat :enabled) "enabled" "disabled"))))

;;;###autoload
(defun lumber-edit-at-point ()
  "Edit the pattern at point in `*Lumber Patterns*'."
  (interactive)
  (let ((pat (lumber--list-get-pattern)))
    (unless pat
      (user-error "No pattern at point"))
    (lumber--edit-pattern pat)))

;;;###autoload
(defun lumber-cycle-fg-at-point ()
  "Cycle foreground color for the pattern at point."
  (interactive)
  (let ((pat (lumber--list-get-pattern)))
    (unless pat (user-error "No pattern at point"))
    (let* ((all-fgs (cl-remove-duplicates
                     (mapcar #'car lumber-default-colors)
                     :test #'equal))
           (current-fg (plist-get pat :foreground))
           (pos (or (cl-position current-fg all-fgs :test #'equal) 0))
           (next-fg (nth (mod (1+ pos) (length all-fgs)) all-fgs)))
      (plist-put pat :foreground next-fg)
      (lumber--after-patterns-changed))))

;;;###autoload
(defun lumber-cycle-bg-at-point ()
  "Cycle background color for the pattern at point."
  (interactive)
  (let ((pat (lumber--list-get-pattern)))
    (unless pat (user-error "No pattern at point"))
    (let* ((all-bgs (cl-remove-duplicates
                     (mapcar #'cdr lumber-default-colors)
                     :test #'equal))
           (current-bg (plist-get pat :background))
           (pos (or (cl-position current-bg all-bgs :test #'equal) 0))
           (next-bg (nth (mod (1+ pos) (length all-bgs)) all-bgs)))
      (plist-put pat :background next-bg)
      (lumber--after-patterns-changed))))

;;;###autoload
(defun lumber-cycle-case-at-point ()
  "Cycle case-sensitive setting for the pattern at point: auto → yes → no → auto."
  (interactive)
  (let ((pat (lumber--list-get-pattern)))
    (unless pat (user-error "No pattern at point"))
    (let* ((current (plist-get pat :case-sensitive))
           (next (cond ((eq current 'auto) t)
                       ((eq current t) nil)
                       (t 'auto))))
      (plist-put pat :case-sensitive next)
      (lumber--after-patterns-changed)
      (message "Case: %s" (cond ((eq next t) "yes")
                                ((eq next nil) "no")
                                (t "auto"))))))

;;;###autoload
(defun lumber-cycle-type-at-point ()
  "Toggle type between literal and regexp for the pattern at point."
  (interactive)
  (let ((pat (lumber--list-get-pattern)))
    (unless pat (user-error "No pattern at point"))
    (let ((new-type (if (eq (plist-get pat :type) 'literal) 'regexp 'literal)))
      (plist-put pat :type new-type)
      (lumber--after-patterns-changed)
      (message "Type: %s" new-type))))

;;;###autoload
(defun lumber-edit-pattern-at-point ()
  "Edit only the pattern string for the pattern at point."
  (interactive)
  (let ((pat (lumber--list-get-pattern)))
    (unless pat (user-error "No pattern at point"))
    (let* ((old-pattern (plist-get pat :pattern))
           (new-pattern (read-string "Pattern: " old-pattern 'lumber--history)))
      (unless (string-equal old-pattern new-pattern)
        (plist-put pat :pattern new-pattern)
        (lumber--after-patterns-changed)
        (message "Updated pattern: %s" new-pattern)))))

(defun lumber--add-color-overlays (&optional buffer)
  "Add high-priority overlays on each Colors cell in BUFFER (default: current buffer).
Locates each cell via the \\='lumber-colors-cell text property set during entry
generation, so overlay placement is independent of column widths or offsets."
  (with-current-buffer (or buffer (current-buffer))
    (remove-overlays (point-min) (point-max) 'lumber-color-ov t)
        (save-excursion
          (goto-char (point-min))
          (while (not (eobp))
            (let* ((id  (tabulated-list-get-id))
                   (pat (when (and (numberp id) (< id (length lumber--patterns)))
                          (nth id lumber--patterns))))
              (when pat
                (let* ((lb  (line-beginning-position))
                       (le  (line-end-position))
                       (beg (text-property-any lb le 'lumber-colors-cell t))
                       (end (when beg
                              (next-single-property-change
                               beg 'lumber-colors-cell nil le))))
                  (when (and beg end)
                    (let ((ov (make-overlay beg end)))
                      (overlay-put ov 'face
                                   (lumber--get-face (plist-get pat :foreground)
                                                     (plist-get pat :background)))
                      (overlay-put ov 'priority 1000)
                      (overlay-put ov 'lumber-color-ov t))))))
            (forward-line 1)))))

(defvar lumber-list-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "a")   #'lumber-add)
    (define-key map (kbd "d")   #'lumber-remove-at-point)
    (define-key map (kbd "t")   #'lumber-toggle-at-point)
    (define-key map (kbd "e")   #'lumber-edit-at-point)
    (define-key map (kbd "RET") #'lumber-edit-at-point)
    (define-key map (kbd "c")   #'lumber-clear)
    (define-key map (kbd "s")   #'lumber-search)
    (define-key map (kbd "g")   #'revert-buffer)
    (define-key map (kbd "w")   #'lumber-save)
    (define-key map (kbd "r")   #'lumber-load)
    (define-key map (kbd "q")   #'quit-window)
    (define-key map (kbd "?")   #'lumber-transient)
    (define-key map (kbd "SPC") #'lumber-toggle-at-point)
    (define-key map (kbd "f")   #'lumber-cycle-fg-at-point)
    (define-key map (kbd "b")   #'lumber-cycle-bg-at-point)
    (define-key map (kbd "C")   #'lumber-cycle-case-at-point)
    (define-key map (kbd "T")   #'lumber-cycle-type-at-point)
    (define-key map (kbd "p")   #'lumber-edit-pattern-at-point)
    map)
  "Keymap for `lumber-list-mode'.")

(define-derived-mode lumber-list-mode tabulated-list-mode "Lumber"
  "Major mode for managing lumber patterns."
  (setq tabulated-list-format
        [("Pattern" 40 t)
         ("S"        3 t)
         ("Type"     8 t)
         ("Case"     5 t)
         ("Colors"  20 nil)])
  (setq tabulated-list-entries #'lumber--list-entries)
  (setq tabulated-list-padding 1)
  (tabulated-list-init-header)
  (when lumber--header-line-remap-cookie
    (face-remap-remove-relative lumber--header-line-remap-cookie)
    (setq lumber--header-line-remap-cookie nil))
  (setq lumber--header-line-remap-cookie
        (face-remap-add-relative 'header-line :weight 'bold))
  (add-hook 'change-major-mode-hook
            (lambda ()
              (when lumber--header-line-remap-cookie
                (face-remap-remove-relative lumber--header-line-remap-cookie)
                (setq lumber--header-line-remap-cookie nil)))
            nil t)
  (add-hook 'after-revert-hook #'lumber--add-color-overlays nil t)
  (setq mode-name
        '(:eval (format "Lumber[%s]"
                        (or lumber--current-set-name "?")))))

;;;; Transient Panel

(transient-define-prefix lumber-transient ()
  "Lumber - Log Pattern Manager"
  ["Pattern Management"
   ("a" "Add pattern"        lumber-add)
   ("A" "Quick add"          lumber-quick-add)
   ("d" "Delete pattern"     lumber-remove)
   ("t" "Toggle enable"      lumber-toggle)
   ("e" "Edit pattern"       lumber-edit)
   ("l" "List patterns"      lumber-list)
   ("c" "Clear all"          lumber-clear)]
  ["Search"
   ("s" "Search (auto)"      lumber-search)
   ("o" "Search (occur)"     lumber-search-occur)
   ("v" "Search (vlf-occur)" lumber-search-vlf-occur)
   ("G" "Search (grep)"      lumber-search-grep)
   ("R" "Search (ripgrep)"   lumber-search-ripgrep)]
  ["Highlight"
   ("h" "Apply highlights"   lumber-apply-highlights)
   ("H" "Clear highlights"   lumber-clear-highlights)]
  ["Pattern Sets"
   ("w" "Save to disk"       lumber-save)
   ("r" "Load from disk"     lumber-load)]
  ["List Buffer Keys (in *Lumber Patterns*)"
   ("SPC" "Toggle at point"     lumber-toggle-at-point)
   ("f"   "Cycle foreground"    lumber-cycle-fg-at-point)
   ("b"   "Cycle background"    lumber-cycle-bg-at-point)
   ("C"   "Cycle case"          lumber-cycle-case-at-point)
   ("T"   "Cycle type"          lumber-cycle-type-at-point)
   ("p"   "Edit pattern string" lumber-edit-pattern-at-point)]
  ["Window"
   ("z" "Toggle result height" lumber-toggle-result-window)])

;;;; Command Map

;;;###autoload
(defvar lumber-command-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "a") #'lumber-add)
    (define-key map (kbd "A") #'lumber-quick-add)
    (define-key map (kbd "d") #'lumber-remove)
    (define-key map (kbd "t") #'lumber-toggle)
    (define-key map (kbd "e") #'lumber-edit)
    (define-key map (kbd "l") #'lumber-list)
    (define-key map (kbd "c") #'lumber-clear)
    (define-key map (kbd "s") #'lumber-search)
    (define-key map (kbd "h") #'lumber-apply-highlights)
    (define-key map (kbd "H") #'lumber-clear-highlights)
    (define-key map (kbd "w") #'lumber-save)
    (define-key map (kbd "r") #'lumber-load)
    (define-key map (kbd "z") #'lumber-toggle-result-window)
    (define-key map (kbd "?") #'lumber-transient)
    map)
  "Keymap for lumber commands. Bind to a prefix key, e.g.:
  (global-set-key (kbd \"C-c l\") lumber-command-map)")

;;;; Window Management

(defun lumber--find-result-window ()
  "Find the visible result window (Occur / VLF-occur / grep / rg)."
  (cl-find-if (lambda (w)
                (let ((name (buffer-name (window-buffer w))))
                  (string-match-p "\\*\\(Occur\\|VLF-occur\\|grep\\|lumber-rg\\)" name)))
              (window-list)))

;;;###autoload
(defun lumber-toggle-result-window ()
  "Toggle the result window between default and expanded height."
  (interactive)
  (let ((win (lumber--find-result-window)))
    (unless win
      (user-error "No result window found"))
    (let* ((frame-h   (frame-height))
           (cur-h     (window-total-height win))
           (ratio     (/ (float cur-h) frame-h))
           (mid       (/ (+ lumber-result-window-height
                            lumber-result-window-height-max)
                         2.0))
           (target    (if (< ratio mid)
                          lumber-result-window-height-max
                        lumber-result-window-height)))
      (with-selected-window win
        (enlarge-window (- (round (* frame-h target))
                           (window-total-height)))))))

;;;; Display Buffer Rules

(add-to-list 'display-buffer-alist
             '("\\*\\(Occur\\|VLF-occur\\|grep\\|lumber-rg\\).*"
               (display-buffer-reuse-window display-buffer-at-bottom)
               (dedicated . t)
               (window-height . (lambda (win)
                                  (window-resize win
                                    (- (round (* (frame-height)
                                                 lumber-result-window-height))
                                       (window-total-height win))
                                    nil nil 'safe)))))

;;;; Persistence

;;;###autoload
(defun lumber-save ()
  "Save current patterns to disk under the current set name.
Prompts for a name if `lumber--current-set-name' is nil."
  (interactive)
  (unless lumber--current-set-name
    (let ((name (read-string "Save as: ")))
      (when (string-empty-p name)
        (user-error "Set name cannot be empty"))
      (setq lumber--current-set-name name)))
  (let* ((existing (when (file-readable-p lumber-persist-file)
                     (with-temp-buffer
                       (insert-file-contents lumber-persist-file)
                       (goto-char (point-min))
                       (condition-case err
                           (read (current-buffer))
                         (error
                          (user-error "Persist file is corrupt, aborting save: %s"
                                      err))))))
         (alist (or existing nil))
         (entry (assoc lumber--current-set-name alist)))
    (if entry
        (setcdr entry (copy-tree lumber--patterns))
      (setq alist (append alist (list (cons lumber--current-set-name
                                            (copy-tree lumber--patterns))))))
    (with-temp-file lumber-persist-file
      (let ((print-level nil)
            (print-length nil))
        (prin1 alist (current-buffer))
        (insert "\n"))))
  (message "Saved set '%s' to %s" lumber--current-set-name lumber-persist-file))

;;;###autoload
(defun lumber-load ()
  "Load a pattern set from `lumber-persist-file'."
  (interactive)
  (unless (file-readable-p lumber-persist-file)
    (user-error "No persist file found: %s" lumber-persist-file))
  (let* ((alist (with-temp-buffer
                  (insert-file-contents lumber-persist-file)
                  (goto-char (point-min))
                  (condition-case err
                      (read (current-buffer))
                    (error
                     (user-error "Failed to read persist file: %s" err)))))
         (name (if (= (length alist) 1)
                   (caar alist)
                 (completing-read "Load set: " (mapcar #'car alist) nil t)))
         (patterns (cdr (assoc name alist))))
    (setq lumber--current-set-name name)
    (setq lumber--patterns (copy-tree patterns))
    (lumber--after-patterns-changed)
    (message "Loaded set '%s' (%d patterns)" name (length lumber--patterns))))

;;;; Integration Points

;; Occur hook: re-apply highlights after *Occur* is populated
(defun lumber--apply-highlights-in-occur ()
  "Apply lumber highlights in the *Occur* buffer after search."
  (when lumber--patterns
    (run-with-idle-timer 0.05 nil
                         (lambda ()
                           (when-let ((buf (get-buffer "*Occur*")))
                             (lumber--apply-highlights buf))))))

(add-hook 'occur-hook #'lumber--apply-highlights-in-occur)

;; Compilation/grep finish hook
(defun lumber--apply-highlights-in-compilation (buf _status)
  "Apply lumber highlights in BUF if it is a lumber results buffer."
  (when lumber--patterns
    (let ((name (buffer-name buf)))
      (when (string-match-p "\\*\\(grep\\|lumber-rg\\)" name)
        (lumber--apply-highlights buf)))))

(add-hook 'compilation-finish-functions #'lumber--apply-highlights-in-compilation)

;; VLF integration: re-apply highlights when navigating chunks
(defun lumber--apply-highlights-if-active ()
  "Apply highlights if lumber has active patterns and hi-lock is on."
  (when lumber--patterns
    (lumber--apply-highlights)))

(with-eval-after-load 'vlf
  (advice-add 'vlf-move-to-chunk :after
              (lambda (&rest _)
                (when lumber--patterns
                  (run-with-idle-timer 0.05 nil
                                       #'lumber--apply-highlights-if-active))))
  ;; Apply highlights after vlf-occur populates its results buffer
  (advice-add 'vlf-occur :after
              (lambda (&rest _)
                (when lumber--patterns
                  (run-with-idle-timer 0.1 nil
                                       (lambda ()
                                         (dolist (buf (buffer-list))
                                           (when (string-match-p "\\*VLF-occur"
                                                                  (buffer-name buf))
                                             (lumber--apply-highlights buf)))))))))

(provide 'lumber)
;;; lumber.el ends here
