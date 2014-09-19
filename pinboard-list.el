;;; pinboard-list.el --- Emacs client for Pinboard.in -*- lexical-binding: t -*-

;; Copyright (C) 2014 Jon Oddie <jonxfield@gmail.com>

;; Author:			Jon Oddie <jonxfield at gmail.com>
;; Created:			22 August 2014
;; Updated:			18 September 2014
;; Version:                     0.4
;; Url:                         https://github.com/joddie/pinboard-list.el
;; Package-Requires:            ((emacs "24") (cl-lib "0.3") (pinboard-api "0.1") (queue "0.1.1"))

;; This file is NOT part of GNU Emacs.

;; This program is free software: you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation, either version 3 of the
;; License, or (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see `http://www.gnu.org/licenses/'.

;;;; Commentary:

;; An Emacs Pinboard.in client in the style of Dired or the built-in
;; `list-bookmarks'.  Includes marking, filtering, and bulk
;; tag/rename/delete operations, as well as editing of bookmark
;; titles, tags and annotations.  Bulk operations are queued and
;; executed asynchronously to respect Pinboard's API rate limiting.

;; Use `pinboard-login' to log in with username and password, or
;; customize `pinboard-api-token'.

;; Use `pinboard-list-bookmarks' to list all your bookmarks,
;; `pinboard-list-tags' to list all tags with bookmark counts.  Use
;; `describe-mode' for a list of keybindings.  Most commands from
;; `dired' or `list-bookmarks' have equivalents: viewing, renaming,
;; annotating, marking, deleting.  There are also commands to filter
;; by tag (`pinboard-add-tag-filter'), by unread status
;; (`pinboard-filter-unread') or untagged
;; (`pinboard-filter-untagged').  `revert-buffer' (normally bound to
;; "g") will fetch any updates from the server.

;;; Suggested keybinding:
;;
;; (global-set-key (kbd "C-x r p") 'pinboard-global-map)
;;
;; This will bind "C-x r p l" to `pinboard-list-bookmarks' and "C-x r
;; p t" to `pinboard-list-tags'.

;;; TODO:
;; - Rename (merge) multiple tags in one operation
;; - Clean up and unify buffer filtering functions
;; - Filter refreshed bookmarks.

;;;; Code:
(require 'cl-lib)
(require 'gv)
(require 'pcase)
(require 'pinboard-api)
(require 'subr-x nil t)
(require 'queue)
(require 'parse-time)
(require 'json)

(defvar pinboard-api-endpoint "https://api.pinboard.in/v1/"
  "Base URL for the Pinboard API, ending in a slash.")

(defvar pinboard-timeout 10
  "Seconds to wait before giving up on an asynchronous Pinboard API call.")

(defvar pinboard-bookmarks nil
  "Hash table mapping URLs to `pinboard-bmk' structs.")

(defvar pinboard-tags nil
  "Hash table mapping Pinboard tag names to bookmark counts.")

(defvar pinboard-work-queue (make-queue)
  "Queue of asynchronously scheduled Pinboard calls and callbacks.
See `pinboard--enqueue' and `pinboard--process-queue'.")

(defvar pinboard-cache-file
  (expand-file-name ".pinboard.eld" user-emacs-directory)
  "File in which to cache Pinboard bookmarks returned from server.")

(defvar pinboard--last-request-time
  (make-hash-table :test 'equal)
  "Hash table recording last Pinboard API request times.")

(defvar pinboard--back-off-time
  (make-hash-table :test 'equal)
  "Hash table of Pinboard API methods that need extra rate-limiting.

Methods are added to this table on returning HTTP status
429 (\"Too Many Requests\").  Each subsequent 429 status doubles
the back-off time.  A successful request clears the method from
the list.")

;;;###autoload
(defvar pinboard-global-map
  (let ((map (make-sparse-keymap)))
    (define-key map "l" #'pinboard-list-bookmarks)
    (define-key map "f" #'pinboard-list-bookmarks-filtered)
    (define-key map "t" #'pinboard-list-tags)
    (define-key map "b" #'pinboard-bookmark-jump)
    map)
  "Keymap with bindings for top-level pinboard-list commands.

This is intended to be bound to a prefix key, for example:
\(global-set-key (kbd \"C-x r p\") 'pinboard-global-map)")
;;;###autoload
(defalias 'pinboard-global-map pinboard-global-map)

;;;###autoload
(defun pinboard--clear-cache ()
  "Clear all locally-cached Pinboard data.

Removes all Pinboard bookmarks and tags from memory and removes
`pinboard-cache-file' when it exists."
  (interactive)
  (setq pinboard-bookmarks nil)
  (setq pinboard-tags nil)
  (setq pinboard-work-queue (make-queue))
  (when (file-exists-p pinboard-cache-file)
    (delete-file pinboard-cache-file)))

;;;; Defvars from URL package
(defvar url-http-response-status)
(defvar url-http-end-of-headers)


;;;; Useful functions from subr-x for older emacs
(eval-and-compile
  (if (fboundp 'hash-table-keys)
      (defalias 'pinboard-hash-table-keys 'hash-table-keys)
    (defun pinboard-hash-table-keys (hash-table)
      "Return a list of keys in HASH-TABLE."
      (let ((keys '()))
	(maphash (lambda (k _v) (push k keys)) hash-table)
	keys)))

  (if (fboundp 'hash-table-values)
      (defalias 'pinboard-hash-table-values 'hash-table-values)
    (defun pinboard-hash-table-values (hash-table)
      "Return a list of values in HASH-TABLE."
      (let ((values '()))
	(maphash (lambda (_k v) (push v values)) hash-table)
	values)))

  (if (fboundp 'string-trim)
      (defalias 'pinboard-string-trim 'string-trim)
    (defun pinboard-string-trim (string)
      "Remove leading and trailing whitespace from STRING."
      (cl-flet ((string-trim-left (string)
                  (if (string-match "\\`[ \t\n\r]+" string)
                      (replace-match "" t t string)
                    string))
                (string-trim-right (string)
                  (if (string-match "[ \t\n\r]+\\'" string)
                      (replace-match "" t t string)
                    string))))
      (string-trim-left (string-trim-right string))))

  (if (fboundp 'define-error)
      (defalias 'pinboard-define-error 'define-error)
    (defun pinboard-define-error (name message &optional parent)
      "Define NAME as a new error signal.
MESSAGE is a string that will be output to the echo area if such an error
is signaled without being caught by a `condition-case'.
PARENT is either a signal or a list of signals from which it inherits.
Defaults to `error'."
      (unless parent (setq parent 'error))
      (let ((conditions
	     (if (consp parent)
		 (apply #'nconc
			(mapcar (lambda (parent)
				  (cons parent
					(or (get parent 'error-conditions)
					    (error "Unknown signal `%s'" parent))))
				parent))
	       (cons parent (get parent 'error-conditions)))))
	(put name 'error-conditions
	     (delete-dups (copy-sequence (cons name conditions))))
	(when message (put name 'error-message message))))))


;;;; Basic structures and variables
(cl-defstruct pinboard-bmk
  title
  annotation
  url
  tags
  shared
  unread
  time)

(defun pinboard-bmk-tag-string (bookmark)
  "Return BOOKMARK's tags as a space-separated string."
  (mapconcat 'identity (pinboard-bmk-tags bookmark) " "))

(defsubst pinboard-bookmark (url)
  "Return the `pinboard-bmk' struct corresponding to URL."
  (gethash url pinboard-bookmarks))

(defun pinboard--bookmarks-tags (bookmarks)
  "Return all the tags used by BOOKMARKS, as a hash-table.

BOOKMARKS is a list of `pinboard-bmk' structs.

The tags are the hash-values of the returned hash table."
  (let ((tags (make-hash-table :test 'pinboard-case-fold)))
    (dolist (bmk bookmarks)
      (dolist (tag (pinboard-bmk-tags bmk))
        (puthash tag t tags)))
    tags))

(defun pinboard-case-fold (a b)
  "Non-nil if strings A and B are equal except for case."
  (eq t (compare-strings a nil nil b nil nil t)))

;; Hash table test for case-insensitive hash tables (for tags etc.)
(define-hash-table-test 'pinboard-case-fold
    #'pinboard-case-fold
  (lambda (a) (sxhash (upcase a))))


;;;; Communication with server

(defun pinboard-retrieve (url synchronous callback)
  "Retrieve URL either synchronously or asynchronously.

SYNCHRONOUS specifies a blocking
request (`url-retrieve-synchronously') or
non-blocking (`url-retrieve').

CALLBACK should be a function of one argument, which will be the
status returned by `url-retrieve', or nil for a blocking call.

If URL is an HTTP url, point will be moved to the end of HTTP
headers in the result buffer before calling CALLBACK."
  (if synchronous
      ;; Synchronous
      (with-current-buffer (url-retrieve-synchronously url)
        (when (boundp 'url-http-end-of-headers)
          (goto-char url-http-end-of-headers))
        (funcall callback nil))
    
    ;; Asynchronous
    (url-retrieve
     url
     (lambda (status)
       (when (boundp 'url-http-end-of-headers)
         (goto-char url-http-end-of-headers))
       (funcall callback status))
     nil t)))

;;; Rate limiting
(defun pinboard--rate-limit (method)
  "Return the Pinboard.in rate limit for METHOD.

This is the number of seconds that must elapse between successive
API calls to METHOD.  These limits are defined by Pinboard and
should not be changed here.  See http://pinboard.in/api/."
  (pcase method
    ("posts/all" (* 5 60))
    ("posts/recent" 60)
    (_ 3)))

(defun pinboard--rate-limit-key (method)
  "Return the hash-key representing METHOD in `pinboard--last-request-time'.
The same hash keys are also used in `pinboard--back-off-time'."
  (pcase method
    ((or "posts/all" "posts/recent") method)
    (_ t)))

;; Request times
(defun pinboard--last-request-time (method)
  "Return the time of the last call to METHOD."
  (gethash (pinboard--rate-limit-key method)
           pinboard--last-request-time
           0))

(gv-define-setter pinboard--last-request-time (value method)
  `(puthash (pinboard--rate-limit-key ,method)
            ,value
            pinboard--last-request-time))

(defun pinboard--record-request-time (method)
  "Record current time as the time of the most recent call to METHOD."
  (setf (pinboard--last-request-time method)
        (float-time)))

;; Extra back-off times
(defun pinboard--back-off-time (method)
  "Return the extra rate-limiting time for METHOD, if any.

Methods require extra rate limiting when the Pinboard API server
returns HTTP status 429."
  (gethash (pinboard--rate-limit-key method)
           pinboard--back-off-time))

(gv-define-setter pinboard--back-off-time (value method)
  `(puthash (pinboard--rate-limit-key ,method)
            ,value
            pinboard--back-off-time))

(defun pinboard--increase-back-off-time (method)
  "Increase time to wait before calling METHOD again.

The time to wait will initially be set to twice the normal
interval between requests, then doubled with each successive 429
status."
  (let ((current-back-off-time (pinboard--back-off-time method)))
    (setf (pinboard--back-off-time method)
          (* 2
             (or
              ;; Double the current back-off time
              current-back-off-time
               ;; Double the normal rate limit
              (pinboard--rate-limit method))))
    (warn "Received HTTP 429 Too Many Requests for %s; waiting minimum %d seconds before next call."
          method (pinboard--back-off-time method))))

(defun pinboard--clear-back-off-time (method)
  "Remove extra rate-limiting for METHOD."
  (setf (pinboard--back-off-time method) nil))

(defun pinboard--too-many-requests-p ()
  "Return t if current buffer contains an HTTP response with status code 429.

The Pinboard API responds with status 429, Too Many Requests to
indicate the need for additional request rate-limiting."
  (equal url-http-response-status 429))

(defun pinboard--wait-time (method)
  "Return the number of seconds to wait before calling METHOD again.

Normally, this is determined by the limits set by the Pinboard
API and defined in `pinboard--rate-limit'.  In case of HTTP 429
Too Many Requests responses, wait times will increase by a factor
of two with each failure."
  (let ((back-off-time (pinboard--back-off-time method))
        (rate-limit (pinboard--rate-limit method))
        (elapsed-time
         (- (float-time)
            (pinboard--last-request-time method))))
    (or back-off-time
        (if (< elapsed-time rate-limit)
            (- rate-limit elapsed-time)
          0))))

(defun pinboard-retrieve-json (method arguments synchronous callback
                               &rest json-arguments)
  "Call Pinboard API method METHOD with ARGUMENTS, and decode response.

SYNCHRONOUS selects a blocking or non-blocking request.  This
function respects Pinboard's rate limits.  If rate-limiting is
needed, as determined by `pinboard--wait-time', it will either
block or use a timer before making the request, depending on the
value of SYNCHRONOUS.

CALLBACK should be a function which takes two arguments, (SUCCESS
RESPONSE).  If the API call succeeds, it is called with t for
SUCCESS and a Lisp object representing the decoded JSON for
RESPONSE.  If there is an error, it is called with nil for both
arguments.

Any additional arguments JSON-ARGUMENTS should be keyword
arguments for `pinboard-json-read' specifying how to decode the
JSON response into Lisp objects."
  (cl-flet ((make-request ()
              (pinboard--record-request-time method)
              (let ((url
                     (concat
                      pinboard-api-endpoint method "?"
                      (url-build-query-string
                       `((format json)
                         (auth_token ,pinboard-api-token)
                         ,@arguments)))))
                (pinboard-retrieve
                 url synchronous
                 (lambda (_)
                   (if (pinboard--too-many-requests-p)
                       ;; Increase wait time before next request
                       (progn
                         (pinboard--increase-back-off-time method)
                         (funcall callback nil nil))
                     (pinboard--clear-back-off-time method)
                     (condition-case nil
                         (let ((response (apply #'pinboard-json-read json-arguments)))
                           (funcall callback t response))
                       (json-readtable-error
                        (funcall callback nil nil)))))))))
    (let* ((wait-time (pinboard--wait-time method))
           (rate-limited (plusp wait-time)))
      (if synchronous
          (progn
            (when rate-limited (sit-for wait-time))
            (make-request))
        (if rate-limited
            (run-with-timer wait-time nil #'make-request)
          (make-request))))))

(cl-defun pinboard-json-read (&key
                                (object-type 'plist)
                                (array-type 'list)
                                (key-type 'keyword))
  "Wrapper for `json-read', specifying result types as arguments."
  (let ((json-object-type object-type)
        (json-array-type array-type)
        (json-key-type key-type))
    (json-read)))

;;; Success/fail requests
(defun pinboard-request (method arguments synchronous callback)
  "Perform a success/fail Pinboard API call to METHOD with ARGUMENTS.

SYNCHRONOUS selects a blocking or asynchronous call.  CALLBACK
should be a function taking one argument, a success indicator.
It is called with a non-nil value if the operation succeeds and
nil if there is any error or if the operation times out, as
determined by `pinboard-timeout'."
  (let ((timeout-timer
         (run-with-timer
          pinboard-timeout nil
          (lambda ()
            (message "Pinboard timeout")
            (funcall callback nil)))))
    (pinboard-retrieve-json
     method arguments synchronous
     (lambda (success response)
       (cancel-timer timeout-timer)
       (funcall callback
                (and success
                     (equal response '(:result_code "done"))))))))

;;; Work queue
(defun pinboard--enqueue (item)
  "Push ITEM onto the Pinboard work queue and start the queue if needed.

ITEM should be a list with one of two forms:
(pinboard-request METHOD ARGUMENTS CALLBACK)
(funcall CALLBACK)."
(let ((empty (queue-empty pinboard-work-queue)))
    (queue-enqueue pinboard-work-queue item)
    (when empty
      ;; (message "Starting queue")
      (run-with-timer 0 nil #'pinboard--process-queue))))

(defun pinboard--enqueue-request (method arguments callback)
  "Add an API request to the Pinboard work queue.

METHOD, ARGUMENTS and CALLBACK have the same meanings as in `pinboard-request'."
  (pinboard--enqueue
   `(pinboard-request ,method ,arguments ,callback)))

(defun pinboard--enqueue-callback (callback)
  "Add CALLBACK, a function of no arguments, to the Pinboard work queue."
  (pinboard--enqueue
   `(funcall ,callback)))

(defun pinboard--process-queue ()
  "Remove a single item from the front of the Pinboard work queue and process it."
  (let ((item (queue-dequeue pinboard-work-queue)))
    ;; (message "Dequeued: %S" item)
    (pcase item
      (`nil nil)
      (`(pinboard-request ,endpoint ,arguments ,callback)
        (pinboard-request
         endpoint arguments nil
         (lambda (success)
           (funcall callback success)
           ;; (message "Processing next queue item")
           (pinboard--process-queue))))
      (`(funcall ,callback)
        (funcall callback)
        (pinboard--process-queue))
      (_
       (error "Bad item in pinboard--process-queue: %S" item)))))


;;;; Higher-level API functions

;;; Login
(defun pinboard-login ()
  "Retrieve Pinboard API token by logging in with username and password."
  (interactive)
  (let ((username (read-string "Pinboard username: "))
        (password (read-passwd "Pinboard password (will not be saved): ")))
    (pinboard-retrieve
     (format "https://%s:%s@api.pinboard.in/v1/user/api_token&format=json"
             (url-hexify-string username)
             (url-hexify-string password))
     t
     (lambda (_)
       (pcase (pinboard-json-read)
         (`(:result ,token)
           (setq pinboard-api-token (concat username ":" token))
           (message "API token set. Use M-x customize-variable RET pinboard-api-token RET to save permanently."))
         (_
          (error "Pinboard login failed")))))))

(defun pinboard-maybe-login ()
  "Login and retrieve Pinboard API token if `pinboard-api-token' is unset."
  (when (or (not pinboard-api-token)
            (string= pinboard-api-token "username:hexstring"))
    (pinboard-login)))

;;; Fetch and cache bookmarks
(pinboard-define-error 'pinboard-rate-limited "Fetching bookmarks is rate limited")

(defun pinboard-fetch-bookmarks (synchronous callback &optional force-update)
  "Fetch Pinboard bookmarks from server if necessary.

SYNCHRONOUS specifies a blocking or non-blocking call.  CALLBACK
should be a function of one argument, a list of all bookmarks
fetched."
  (cl-labels
      ((load-from-cache-with-fallback ()
         (pinboard--load-from-cache
          (lambda () (success "Cached bookmarks may be out of date"))
          (lambda ()
            (pinboard--remove-cache)
            (pinboard--fetch-bookmarks-from-server synchronous #'success #'failure))))
       
       (fetch-from-server-with-fallback ()
         (pinboard--fetch-bookmarks-from-server
          synchronous
          #'success
          (lambda ()
            (pinboard--load-from-cache
             (lambda ()
               (success "Showing cached bookmarks (possibly out of date)"))
             #'failure))))
       
       (success (&optional msg)
         (when msg (message "%s" msg))
         (funcall callback (hash-table-values pinboard-bookmarks)))
       
       (failure (&optional (msg "Bookmark loading failed."))
         (when msg (message "%s" msg))
         (funcall callback nil)))
    
    (cond
      ((not (null pinboard-bookmarks))
       (if force-update
           (pinboard--fetch-bookmarks-from-server
            synchronous
            #'success
            (lambda () (success "Bookmarks may be out of date.")))
         ;; not force-update
         (success)))
      
      ((pinboard--cache-exists-p)       ; not in-memory
       (pinboard--fetch-update-time
        synchronous
        (lambda (update-time)
          (if (pinboard--cache-up-to-date-p update-time)
              (load-from-cache-with-fallback)
            (fetch-from-server-with-fallback)))
        (lambda ()
          (pinboard--load-from-cache
           (lambda () (success "Bookmarks may be out of date."))
           #'failure))))

      (t                                ; neither in memory nor in cache
       (pinboard--fetch-bookmarks-from-server
        synchronous
        #'success
        #'failure)))))

(defun pinboard--fetch-update-time (synchronous on-success on-failure)
  (pinboard-retrieve-json
   "posts/update" nil synchronous
   (lambda (success response)
     (if success
         (let ((update-time
                (pinboard-parse-time-string
                 (plist-get response :update_time))))
           (funcall on-success update-time))
       (funcall on-failure)))))

(defun pinboard--fetch-bookmarks-from-server (synchronous on-success on-failure)
  (let ((posts-all-wait (pinboard--wait-time "posts/all"))
        (posts-recent-wait (pinboard--wait-time "posts/recent")))
    (cond ((and (plusp posts-all-wait) (plusp posts-recent-wait))
           (funcall on-failure))
          ((<= posts-all-wait posts-recent-wait)
           (pinboard--fetch-all-from-server synchronous on-success on-failure))
          (t
           (pinboard--fetch-recent-from-server synchronous on-success on-failure)))))

(defun pinboard--fetch-all-from-server (synchronous on-success on-failure)
  (let ((progress (make-progress-reporter
                   "Loading all bookmarks from server ...")))
    (pinboard-retrieve-json
     "posts/all" nil
     synchronous
     (lambda (success response)
       (if (not success)
           (funcall on-failure)
         (progress-reporter-done progress)
         (pinboard--cache-response response)
         (pinboard--parse-bookmarks response nil)
         (funcall on-success))))))

(defun pinboard--fetch-recent-from-server (synchronous on-success on-failure)
  (let ((progress (make-progress-reporter
                   "Loading recent bookmarks from server ...")))           
    (pinboard-retrieve-json
     "posts/recent" `((count 100))
     synchronous
     (lambda (success response)
       (if (not success)
           (funcall on-failure)
         (progress-reporter-done progress)
         (pinboard--parse-bookmarks (plist-get response :posts) t)
         (funcall on-success))))))

;;; Cache file handling
(defun pinboard--cache-exists-p ()
  (file-exists-p pinboard-cache-file))

(defun pinboard--cache-response (response)
  (with-temp-file pinboard-cache-file
    (let ((print-level nil)
          (print-length nil))
      (print response (current-buffer)))))

(defun pinboard--remove-cache ()
  (ignore-errors
    (delete-file pinboard-cache-file)))

(defun pinboard--cache-up-to-date-p (update-time)
  (let* ((cache-time (nth 5 (file-attributes pinboard-cache-file))))
    (and cache-time
         (time-less-p update-time cache-time))))

(defun pinboard--load-from-cache (on-success on-failure)
  (condition-case _
      (with-temp-buffer
        (insert-file-contents pinboard-cache-file)
        (pinboard--parse-bookmarks (read (copy-marker (point-min))))
        (funcall on-success))
    (error
     (funcall on-failure))))

;;; Bookmark JSON parsing
(defun pinboard--parse-bookmarks (response &optional partial)
  "Create `pinboard-bmk' structs for the parsed server JSON in RESPONSE.

PARTIAL specifies that RESPONSE contains only recent bookmarks.
In this case the contents of `pinboard-bookmarks' and
`pinboard-tags' should be updated rather than replaced"
  ;; Make new, empty hash tables for `pinboard-bookmarks' and
  ;; `pinboard-tags' either when (a) all bookmarks are being loaded,
  ;; so we can safely erase the old data, or (b) the variable is `nil'
  ;; due to a cleared cache
  (when (or (not partial) (not pinboard-bookmarks))
    (setq pinboard-bookmarks (make-hash-table :test 'equal)))
  (when (or (not partial) (not pinboard-tags))
    (setq pinboard-tags (make-hash-table :test 'pinboard-case-fold)))

  (let ((progress (make-progress-reporter "Parsing bookmarks"
                                          0 (length response) 0 10))
        (i 0))
    (dolist (elt response)
      (progress-reporter-update progress (incf i))
      (let ((bmk (pinboard--parse-bookmark elt)))
        (puthash (pinboard-bmk-url bmk) bmk pinboard-bookmarks)
        (unless partial
          (dolist (tag (pinboard-bmk-tags bmk))
            (incf (gethash tag pinboard-tags 0))))))
    (progress-reporter-done progress)))

(defun pinboard--parse-bookmark (json)
  "Create a `pinboard-bmk' struct for a single JSON response from server."
  (cl-destructuring-bind
        (&key href description extended tags toread shared time
              &allow-other-keys)
      json
    (make-pinboard-bmk
     :title description
     :annotation extended
     :url href
     :tags (split-string tags)
     :unread (string= toread "yes")
     :shared (string= shared "yes")
     :time time)))

;; Recent Emacs have parse-time-iso8601-regexp, but it is undocumented
;; and does not seem to work on times that end with "Z" for UTC, as
;; Pinboard's updated-times currently do.  Raise an Emacs bug for
;; this?
(defvar pinboard-time-regexp
  (rx (group (repeat 4 digit))
      "-"
      (group (repeat 2 digit))
      "-"
      (group (repeat 2 digit))
      "T"
      (group (repeat 2 digit))
      ":"
      (group (repeat 2 digit))
      ":"
      (group (repeat 2 digit))
      "Z"))

(defun pinboard-parse-time-string (time)
  "Parse TIME, an ISO8601 date matching `pinboard-time-regexp'."
  (if (string-match pinboard-time-regexp time)
      (cl-flet ((match-number (group)
                  (string-to-number (match-string group time))))
        (let ((year (match-number 1))
              (month (match-number 2))
              (day (match-number 3))
              (hour (match-number 4))
              (minute (match-number 5))
              (second (match-number 6)))
          (encode-time second minute hour day month year 0)))
    (error "Pinboard response `%s' does not match expected format" time)))

;;; Update bookmarks
(defun pinboard--update-bookmark (bmk synchronous callback)
  (pinboard-request
   "posts/add"
   (pinboard--bookmark-query bmk)
   synchronous
   (lambda (success)
     (when success
       (puthash (pinboard-bmk-url bmk) bmk pinboard-bookmarks))
     (funcall callback success))))

(defun pinboard--enqueue-bookmark-update (bmk callback)
  (pinboard--enqueue-request
   "posts/add"
   (pinboard--bookmark-query bmk)
   (lambda (success)
     (when success
       (puthash (pinboard-bmk-url bmk) bmk pinboard-bookmarks))
     (funcall callback success))))

(defun pinboard--bookmark-query (bmk)
  `((url ,(pinboard-bmk-url bmk))
    (description ,(pinboard-bmk-title bmk))
    (extended ,(pinboard-bmk-annotation bmk))
    (tags ,(pinboard-bmk-tag-string bmk))
    (shared ,(if (pinboard-bmk-shared bmk) "yes" "no"))
    (toread ,(if (pinboard-bmk-unread bmk) "yes" "no"))
    (replace "yes")))

;;; Fetch tags
(defun pinboard-fetch-tags (synchronous callback)
  (pinboard-retrieve-json
   "tags/get" nil
   synchronous
   (lambda (success response)
     (if (not success)
         (error "Failed to fetch list of tags")
       (setq pinboard-tags
             (make-hash-table :test 'pinboard-case-fold))
       (pcase-dolist (`(,name . ,count) response)
         (puthash name (string-to-number count)
                  pinboard-tags))
       (funcall callback pinboard-tags)))
   :object-type 'alist
   :key-type 'string))


;;;; List-buffer utilities
(defmacro pinboard--do-buffer-lines (&rest body)
  `(save-excursion
     (goto-char (point-min))
     (while (not (eobp))
       ,@body
       (forward-line))))

(defun pinboard--find-buffer-line (predicate)
  (catch 'found
    (pinboard--do-buffer-lines
     (when (funcall predicate)
       (throw 'found (line-number-at-pos))))
    nil))

(defun pinboard--goto-line (line-number)
  (goto-char (point-min))
  (forward-line (1- line-number)))

(defun pinboard--goto-line-where (predicate)
  (let ((line-number (pinboard--find-buffer-line predicate)))
    (when line-number (pinboard--goto-line line-number))))

(defun pinboard--get-mark ()
  (char-after (point-at-bol)))

(cl-defun pinboard--marked-ids (&optional (mark ?>))
  (cl-loop for (id . mark1) in (pinboard--collect-marks)
           if (eq mark mark1)
           collect id))

(defun pinboard--collect-marks ()
  (let ((marks '()))
    (pinboard--do-buffer-lines
     (let ((mark (pinboard--get-mark)))
       (unless (eq mark ?\ )
         (push (cons (tabulated-list-get-id) mark)
               marks))))
    marks))

(defun pinboard--apply-marks (marks)
  (pinboard--do-buffer-lines
   (let* ((id (tabulated-list-get-id))
          (mark (cdr (assoc id marks))))
     (when mark
       (tabulated-list-put-tag (string mark))))))

(defmacro pinboard--with-saved-marks (&rest body)
  (let ((marks (make-symbol "marks"))
        (buffer (make-symbol "buffer")))
    `(let ((,marks (pinboard--collect-marks))
           (,buffer (current-buffer)))
       (unwind-protect
            (progn ,@body)
         (with-current-buffer ,buffer
           (pinboard--apply-marks ,marks))))))

(defun pinboard-tabulated-list-revert (&rest arguments)
  (pinboard--with-saved-marks
   (apply #'tabulated-list-revert arguments)))


;;;; Generic list-buffer mode and commands
(defvar pinboard-tabulated-list-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "m" #'pinboard-mark)
    (define-key map "d" #'pinboard-mark-for-deletion)
    (define-key map (kbd "C-d") #'pinboard-mark-for-deletion-backward)
    (define-key map (kbd "DEL") #'pinboard-unmark-backward)
    (define-key map (kbd "M-DEL") #'pinboard-remove-marks)
    (define-key map (kbd "C-t") #'pinboard-toggle-marks)
    (define-key map (kbd "* c") #'pinboard-change-marks)
    map))

(define-derived-mode pinboard-tabulated-list-mode tabulated-list-mode ""
                     "Generic enhanced tabulated-list-mode for Pinboard modes"
  (setq tabulated-list-padding 1)
  (setq-local revert-buffer-function #'pinboard-tabulated-list-revert))

(defun pinboard-mark ()
  (interactive)
  (tabulated-list-put-tag ">" t))

(defun pinboard-mark-for-deletion ()
  (interactive)
  (tabulated-list-put-tag "D" t))

(defun pinboard-mark-for-deletion-backward ()
  (interactive)
  (tabulated-list-put-tag "D")
  (forward-line -1))

(defun pinboard-unmark-backward ()
  (interactive)
  (forward-line -1)
  (tabulated-list-put-tag "" nil))

(defun pinboard-remove-marks (mark)
  (interactive "cRemove marks (RET means all): ")
  (if (eq mark ?\r) (setq mark nil))
  (pinboard--do-buffer-lines
   (when (or (not mark)
             (eq mark (char-after)))
     (tabulated-list-put-tag ""))))

(defun pinboard-change-marks (&optional old new)
  "Change all OLD marks to NEW marks.
OLD and NEW are both characters used to mark bookmarks."
  ;; taken from dired-change-marks in dired.el
  (interactive
   (let* ((cursor-in-echo-area t)
	  (old (progn (message "Change (old mark): ") (read-char)))
	  (new (progn (message "Change %c marks to (new mark): " old)
		      (read-char))))
     (list old new)))
  (if (or (eq old ?\r) (eq new ?\r))
      (ding)
    (let ((string (string new)))
      (pinboard--do-buffer-lines
       (when (eq (pinboard--get-mark) old)
         (tabulated-list-put-tag string))))))

(defun pinboard-toggle-marks ()
  (interactive)
  (pinboard--do-buffer-lines
   (tabulated-list-put-tag
    (if (eq ?> (pinboard--get-mark)) "" ">"))))


;;;; Bookmark buffer mode
(defvar-local pinboard-displayed-urls nil
  "List of bookmark URLs displayed in this buffer")

(defun pinboard-displayed-bookmarks ()
  (mapcar #'pinboard-bookmark pinboard-displayed-urls))

(defvar-local pinboard-buffer-filters nil
  "List of tag filters applied to current buffer")

(defvar-local pinboard-buffer-tags nil
  "Hash table listing tags of bookmarks in current buffer")

(defvar pinboard-bookmark-columns
  '((unread "R" 1 t :pad-right 0)
    (shared "P" 1 t :pad-right 0)
    (annotation "A" 1 t)
    (title "Title" 40 t)
    (tags "Tags" 30 nil)
    (time "Time" 13 t)
    (url "URL" 30 t)))

(defvar pinboard-visible-columns
  (mapcar #'car pinboard-bookmark-columns))

(defun pinboard--column-value (bmk column)
  (pcase column
    (`unread
     (if (pinboard-bmk-unread bmk) "!" ""))
    (`shared
     (if (pinboard-bmk-shared bmk) "." ""))
    (`annotation
     (if (not (zerop (length (pinboard-bmk-annotation bmk)))) "+" ""))
    (`title
     (pinboard-bmk-title bmk))
    (`tags
     (pinboard-bmk-tag-string bmk))
    (`url
     (pinboard-bmk-url bmk))
    (`time
     (pinboard-bmk-time bmk))
    (_
     (error "Unknown column `%s'" column))))

(defvar pinboard-bookmarks-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "RET") #'pinboard-bookmark-open)
    (define-key map "o" #'pinboard-bookmark-open-other-window)
    (define-key map "r" #'pinboard-rename-bookmark)
    (define-key map "x" #'pinboard-do-flagged-delete-bookmarks)
    (define-key map "w" #'pinboard-where)
    (define-key map "a" #'pinboard-show-annotation)
    (define-key map "A" #'pinboard-show-all-annotations)
    (define-key map "e" #'pinboard-edit-annotation)
    (define-key map "f" #'pinboard-add-tag-filter)
    (define-key map "F" #'pinboard-remove-tag-filter)
    (define-key map (kbd "s u r") #'pinboard-filter-unread)
    (define-key map (kbd "s u t") #'pinboard-filter-untagged)
    (define-key map "k" #'pinboard-kill-bookmark-lines)
    (define-key map (kbd "s a") #'pinboard-show-all)
    (define-key map "c" #'pinboard-toggle-column)
    (define-key map "t" #'pinboard-tag-bookmark)
    (define-key map "T" #'pinboard-untag-bookmark)
    (define-key map "!" #'pinboard-toggle-unread)
    (define-key map "R" #'pinboard-relocate-bookmark)
    (define-key map (kbd "* t") #'pinboard-mark-by-tags)
    (define-key map (kbd "% m") #'pinboard-mark-by-title)
    (define-key map (kbd "% u") #'pinboard-mark-by-url)
    (define-key map "j" #'pinboard-jump-to-bookmark)
    map))

(define-derived-mode pinboard-bookmarks-mode pinboard-tabulated-list-mode
  "Pinboard"
  "Major mode for viewing and editing a list of Pinboard bookmarks.

Commands:
\\[pinboard-bookmark-open] -- visit bookmark on this line
\\[pinboard-bookmark-open-other-window] -- visit bookmark in other window using `eww'
\\[pinboard-where] -- show bookmark URL in the echo area
\\[pinboard-show-annotation] -- show full bookmark details in another window
\\[pinboard-show-all-annotations] -- show details of all bookmarks in another window
\\[pinboard-jump-to-bookmark] -- jump to a bookmark by title
\\[pinboard-toggle-column] -- toggle a displayed column on or off

Filter displayed bookmarks:
\\[pinboard-add-tag-filter] -- filter by tag
\\[pinboard-remove-tag-filter] -- remove a tag filter
\\[pinboard-filter-unread] -- show only unread bookmarks
\\[pinboard-filter-untagged] -- show only untagged bookmarks
\\[pinboard-show-all] -- show all bookmarks (removing all filters)
\\[pinboard-kill-bookmark-lines] -- hide marked bookmarks from display

Edit a single bookmark:
\\[pinboard-relocate-bookmark] -- edit bookmark URL
\\[pinboard-rename-bookmark] -- edit bookmark title
\\[pinboard-edit-annotation] -- edit bookmark details, including annotation

Bulk editing:
These commands operate on all the marked bookmarks, or the
bookmark at point if none are marked.
\\[pinboard-tag-bookmark] -- add tags
\\[pinboard-untag-bookmark] -- remove tags
\\[pinboard-toggle-unread] -- toggle read/unread status

Marking for bulk operations:
\\[pinboard-mark] -- mark bookmark at point
\\[pinboard-mark-by-tags] -- mark by tag
\\[pinboard-mark-by-title] -- mark by title (regexp)
\\[pinboard-mark-by-url] -- mark by URL (regexp)
\\[pinboard-unmark-backward] -- move up and remove marks
\\[pinboard-toggle-marks] -- toggle all marks
\\[pinboard-change-marks] -- substitute one mark for another

Deleting:
\\[pinboard-mark-for-deletion] -- mark bookmark at point for deletion
\\[pinboard-do-flagged-delete-bookmarks] -- delete bookmarks marked for deletion"
  (setq tabulated-list-entries #'pinboard--tabulated-list-entries)
  (add-hook 'tabulated-list-revert-hook #'pinboard--refresh-bookmarks nil t)
  (setq tabulated-list-format
        (pinboard--make-bookmark-list-format
         pinboard-visible-columns
         (window-width)))
  (tabulated-list-init-header))

;;;###autoload
(defun pinboard-list-bookmarks ()
  "List all Pinboard bookmarks in a buffer.

The bookmark-list buffer is in `pinboard-bookmarks-mode': see its
documentation for a list of commands."
  (interactive)
  (pinboard-fetch-bookmarks
   nil
   (lambda (bookmarks)
     (pop-to-buffer
      (pinboard--make-bookmark-list-buffer
       (pinboard--sort-bookmarks-by-time bookmarks))))))

(defun pinboard-list-bookmarks-filtered (tags)
  "List Pinboard bookmarks filtered by one or more tags in a buffer.

The bookmark-list buffer is in `pinboard-bookmarks-mode': see its
documentation for a list of commands."
  (interactive
   (list
    (progn
      (unless pinboard-tags
        (pinboard-maybe-login)
        (pinboard-fetch-tags t 'ignore))
      (pinboard--read-tags "Bookmarks tagged: "))))
  (pinboard-fetch-bookmarks
   nil
   (lambda (bookmarks)
     (with-current-buffer
         (pinboard--make-bookmark-list-buffer
          (pinboard--sort-bookmarks-by-time bookmarks))
       (mapc #'pinboard-add-tag-filter tags)
       (pop-to-buffer (current-buffer))))))

(defun pinboard-bookmark-jump (title)
  (interactive
   (list
    (pinboard-fetch-bookmarks
     t
     (lambda (bookmarks)
       (completing-read "Jump to bookmark: "
                        (mapcar #'pinboard-bmk-title bookmarks)
                        nil t)))))
  ;; FIXME :-/
  (cl-loop for bmk being the hash-values of pinboard-bookmarks
           if (string= (pinboard-bmk-title bmk) title)
           do (pinboard-bookmark-open bmk)
           and return bmk))

(defun pinboard--make-bookmark-list-buffer (bookmarks)
  (with-current-buffer (get-buffer-create "*pinboard*")
    (let ((inhibit-read-only t))
      (erase-buffer)
      (pinboard-bookmarks-mode))
    (pinboard--display-bookmarks
     (pinboard--sort-bookmarks-by-time bookmarks))
    (current-buffer)))

(defun pinboard--sort-bookmarks-by-time (bmks)
  (sort bmks
        (lambda (a b)
          (string<
           (pinboard-bmk-time b)
           (pinboard-bmk-time a)))))

(defun pinboard--make-bookmark-list-format (visible-columns window-width)
  (let ((format
         (apply #'vector
                (cl-loop for (name . definition) in pinboard-bookmark-columns
                         if (memq name visible-columns)
                         collect (copy-sequence definition)))))
    (let* ((total-width
            (cl-loop for column across format
                     sum (+ 1 (nth 1 column))))
           (unused-width
            (- window-width total-width)))
      (when (plusp unused-width)
        (cl-loop for column across format
                 if (equal (nth 0 column) "Title") ; HACK
                 do (incf (nth 1 column) unused-width))))
    format))

(defun pinboard--display-bookmarks (bmks)
  (setq pinboard-displayed-urls (mapcar #'pinboard-bmk-url bmks))
  (setq pinboard-buffer-tags (pinboard--bookmarks-tags bmks))
  (tabulated-list-print t))

(defun pinboard--update-bookmark-list-format ()
  (setq tabulated-list-format
        (pinboard--make-bookmark-list-format
         pinboard-visible-columns
         (window-width)))
  (tabulated-list-init-header)
  (tabulated-list-print t))

(defun pinboard--tabulated-list-entries ()
  (let ((columns
         (cl-loop for (column . _) in pinboard-bookmark-columns
                  if (memq column pinboard-visible-columns)
                  collect column)))
    (cl-loop for url in pinboard-displayed-urls
             collect
             (list url
                   (apply 'vector
                          (cl-loop for column in columns
                                   collect
                                   (pinboard--column-value
                                    (pinboard-bookmark url)
                                    column)))))))

(defun pinboard-bookmark-at-point ()
  (let ((bookmark (pinboard-bookmark (tabulated-list-get-id))))
    (or bookmark
        (error "No bookmark at point"))))

(cl-defun pinboard--marked-bookmarks (&optional (mark ?>))
  (or (mapcar #'pinboard-bookmark (pinboard--marked-ids mark))
      (if (eq mark ?>)
          (list (pinboard-bookmark-at-point))
        nil)))

(defun pinboard--operate-on-bookmarks (for-each finally)
  "Asynchronously update the marked bookmarks (or bookmark at point if none).

FOR-EACH should be a function which takes one argument, a
`pinboard-bmk' struct.  It is called in sequence for each
bookmark to be updated and should make whatever changes are
appropriate to the structure, for example by
using (setf (pinboard-bmk-...) ...).

FINALLY should be a function of two arguments, SUCCESSES and
FAILURES.  It will be called after all bookmarks have been
processed with total counts of successful and failed Pinboard API
calls."
  (let ((bookmarks (pinboard--marked-bookmarks))
        (successes 0) (failures 0))
    (dolist (bmk bookmarks)
      (let ((updated (copy-pinboard-bmk bmk)))
        (funcall for-each updated)
        (unless (equal updated bmk)
          (pinboard--enqueue-bookmark-update
           updated
           (lambda (success)
             (if success (incf successes) (incf failures)))))))
    (pinboard--enqueue-callback
     (lambda ()
       (funcall finally successes failures)))))

(defun pinboard--redraw-bookmark-list ()
  (with-current-buffer "*pinboard*"
    (pinboard--with-saved-marks
     (tabulated-list-print t))))

(defun pinboard--refresh-bookmarks ()
  (interactive)
  (pinboard-fetch-bookmarks
   t
   (lambda (bmks)
     ;; FIXME: Filter refreshed bookmarks.
     (pinboard--display-bookmarks
      (pinboard--sort-bookmarks-by-time bmks)))
   t                                    ; force update
   ))


;;;; Bookmark buffer commands
(defun pinboard-toggle-column (column)
  (interactive
   (list
    (intern
     (completing-read "Toggle column: " pinboard-bookmark-columns nil t))))
  (when (not (assq column pinboard-bookmark-columns))
    (user-error "Unknown column `%s'" column))
  (setq pinboard-visible-columns
        (cl-set-exclusive-or
         pinboard-visible-columns (list column)))
  (pinboard--update-bookmark-list-format))

(defun pinboard-bookmark-open (bookmark)
  (interactive (list (pinboard-bookmark-at-point)))
  (browse-url (pinboard-bmk-url bookmark)))

(defun pinboard-bookmark-open-other-window (bookmark)
  (interactive (list (pinboard-bookmark-at-point)))
  (save-window-excursion
    (eww (pinboard-bmk-url bookmark)))
  (switch-to-buffer-other-window "*eww*"))

(defun pinboard-where (bookmark)
  (interactive (list (pinboard-bookmark-at-point)))
  (message "%s" (pinboard-bmk-url bookmark)))

;;; Filtering commands
(defun pinboard-add-tag-filter (tag)
  (interactive
   (list
    (completing-read "Filter by tag: " pinboard-buffer-tags)))
  (push tag pinboard-buffer-filters)
  (pinboard--display-bookmarks
   (cl-loop for bmk in (pinboard-displayed-bookmarks)
            if (cl-member tag (pinboard-bmk-tags bmk)
                          :test #'pinboard-case-fold)
            collect bmk)))

(defun pinboard-remove-tag-filter (tag)
  (interactive
   (list
    (if pinboard-buffer-filters
        (completing-read "Remove tag filter (RET means all): "
                         pinboard-buffer-filters nil t)
      (user-error "No tag filters in current buffer"))))
  (setq pinboard-buffer-filters
        (if (plusp (length tag))
            (remove tag pinboard-buffer-filters)
          nil))
  (pinboard--display-bookmarks
   (cl-loop for bmk in (pinboard-hash-table-values pinboard-bookmarks)
            if
            (cl-subsetp pinboard-buffer-filters
                        (pinboard-bmk-tags bmk)
                        :test #'pinboard-case-fold)
            ;; (cl-loop for tag in pinboard-buffer-filters
            ;;          always (cl-member tag (pinboard-bmk-tags bmk)
            ;;                            :test #'pinboard-case-fold))
            collect bmk)))

(defun pinboard-filter-unread ()
  (interactive)
  (message "Showing unread bookmarks")
  (pinboard--display-bookmarks
   (cl-remove-if-not
    #'pinboard-bmk-unread
    (pinboard-displayed-bookmarks))))

(defun pinboard-filter-untagged ()
  (interactive)
  (message "Showing untagged bookmarks")
  (pinboard--display-bookmarks
   (cl-remove-if
    #'pinboard-bmk-tags
    (pinboard-displayed-bookmarks))))

(defun pinboard-show-all ()
  (interactive)
  (message "Showing all bookmarks")
  (setq pinboard-buffer-filters nil)
  (pinboard--display-bookmarks
   (pinboard--sort-bookmarks-by-time
    (pinboard-hash-table-values pinboard-bookmarks))))

(defun pinboard-kill-bookmark-lines ()
  "Hide marked bookmarks from display."
  (interactive)
  (let ((marked-urls (pinboard--marked-ids)))
    (message "Hiding %d marked bookmarks" (length marked-urls))
    (pinboard--display-bookmarks
     (cl-remove-if
      (lambda (bmk) (member (pinboard-bmk-url bmk) marked-urls))
      (pinboard-displayed-bookmarks)))))

;;; Editing commands
(defun pinboard-tag-bookmark (&rest tags)
  (interactive
   (let* ((count (length (pinboard--marked-bookmarks)))
          (prompt (format "Add tags to %d bookmark(s): " count)))
     (pinboard--read-tags prompt)))
  (if (not (and (length tags)
                (length (first tags))))
      (message "No tags")
    (pinboard--operate-on-bookmarks
     (lambda (bookmark)
       (message "Tagging `%s'" (pinboard-bmk-title bookmark))
       (setf (pinboard-bmk-tags bookmark)
             (cl-union (pinboard-bmk-tags bookmark)
                       tags
                       :test #'pinboard-case-fold)))
     (lambda (successes failures)
       (message "Tagged %d bookmark(s) with %S, %d failure(s)"
                successes tags failures)
       (pinboard--redraw-bookmark-list)))))

(defun pinboard-untag-bookmark ()
  (interactive)
  (let* ((bmks (pinboard--marked-bookmarks))
         (tags (pinboard-hash-table-keys (pinboard--bookmarks-tags bmks))))
    (if (not tags)
        (message "Bookmark(s) have no tags")
      (let ((tags (pinboard--read-tags
                   (format "Remove tag(s) from %d bookmark(s) (RET means all): "
                           (length bmks))
                   tags)))
        (if (plusp (length tags))
            ;; Remove specified tags
            (pinboard--operate-on-bookmarks
             (lambda (bookmark)
               (message "Untagging `%s'" (pinboard-bmk-title bookmark))
               (setf (pinboard-bmk-tags bookmark)
                     (cl-set-difference (pinboard-bmk-tags bookmark)
                                        tags
                                        :test #'pinboard-case-fold)))
             (lambda (successes failures)
               (message "Removed tag(s) %S from %d bookmarks, [%d failure(s)]"
                        tags successes failures)
               (pinboard--redraw-bookmark-list)))
          ;; Clear all tags
          (pinboard--operate-on-bookmarks
           (lambda (bookmark)
             (message "Untagging `%s'" (pinboard-bmk-title bookmark))
             (setf (pinboard-bmk-tags bookmark) nil))
           (lambda (successes failures)
             (message "Removed all tags from %d bookmarks, [%d failure(s)]"
                      successes failures)
             (pinboard--redraw-bookmark-list))))))))

(defun pinboard-rename-bookmark ()
  (interactive)
  (let* ((bmk (pinboard-bookmark-at-point))
         (updated (copy-pinboard-bmk bmk))
         (title (pinboard-bmk-title bmk))
         (new-title (read-string "Title: " title)))
    (setf (pinboard-bmk-title updated) new-title)
    (pinboard--update-bookmark
     updated t
     (lambda (success)
       (when success
         (message "Renamed bookmark")
         (pinboard--redraw-bookmark-list))))))

(defun pinboard-relocate-bookmark ()
  (interactive)
  (let* ((bmk (copy-pinboard-bmk (pinboard-bookmark-at-point)))
         (old-url (pinboard-bmk-url bmk))
         (new-url (read-string "URL: " old-url))
         (buffer (current-buffer)))
    (setf (pinboard-bmk-url bmk) new-url)
    ;; There is currently no atomic API call to relocate a bookmark
    ;; URL, so we first add the new URL and then delete the old one.
    (pinboard--update-bookmark
     bmk t
     (lambda (success)
       (if (not success)
           (error "Moving bookmark URL failed [1]")
         (pinboard-request
          "posts/delete"
          `((url ,old-url))
          t
          (lambda (success)
            (if (not success)
                (error "Moving bookmark URL failed [2]")
              (message "Moved bookmark URL")
              ;; Update the cache of bookmarks
              (puthash new-url bmk pinboard-bookmarks)
              (remhash old-url pinboard-bookmarks)
              ;; Update the buffer-local list of displayed bookmarks
              (with-current-buffer buffer
                (setq pinboard-displayed-urls
                      (cl-substitute new-url old-url
                                     pinboard-displayed-urls
                                     :test 'equal)))
              ;; Redraw
              (pinboard--redraw-bookmark-list)))))))))

(defun pinboard-toggle-unread ()
  (interactive)
  (let ((marked-read 0) (marked-unread 0))
    (pinboard--operate-on-bookmarks
     (lambda (bookmark)
       (let ((unread (not (pinboard-bmk-unread bookmark))))
         (message "Marking bookmark `%s' %s"
                  (pinboard-bmk-title bookmark)
                  (if unread "unread" "read"))
         (setf (pinboard-bmk-unread bookmark) unread)
         (if unread
             (incf marked-unread)
           (incf marked-read))))
     (lambda (_successes failures)
       (message "Marked %d bookmarks as read, %d as unread [%d errors]"
                marked-read marked-unread failures)
       (pinboard--redraw-bookmark-list)))))

(defun pinboard-do-flagged-delete-bookmarks ()
  (interactive)
  (let* ((bookmarks (pinboard--marked-bookmarks ?D))
         (count (length bookmarks))
         (prompt
          (if (> count 1)
              (format "Permanently delete %d bookmarks?" count)
            (format "Permanently delete bookmark `%s'?"
                    (pinboard-bmk-title (first bookmarks))))))
    (if (yes-or-no-p prompt)
        (let ((successes 0) (failures 0)
              (buffer (current-buffer)))
          (dolist (bmk bookmarks)
            (let ((url (pinboard-bmk-url bmk)))
              (message "Deleting bookmark `%s'" (pinboard-bmk-title bmk))
              (pinboard--enqueue-request
               "posts/delete"
               `((url ,url))
               (lambda (success)
                 (if success
                     (progn
                       (incf successes)
                       (remhash url pinboard-bookmarks)
                       (with-current-buffer buffer
                         (setq pinboard-displayed-urls
                               (remove url pinboard-displayed-urls))))
                   (incf failures))))))
          (pinboard--enqueue-callback
           (lambda ()
             (message "Deleted %d bookmark(s) [%d error(s)]"
                      successes failures)
             (pinboard--redraw-bookmark-list)))))))

;;; Annotation/popup commands
(defun pinboard-show-annotation ()
  (interactive)
  (pinboard--popup-bookmark nil))

(defun pinboard-edit-annotation ()
  (interactive)
  (pinboard--popup-bookmark t))

(defun pinboard-show-all-annotations ()
  (interactive)
  (let ((bmks (pinboard-displayed-bookmarks)))
    (with-current-buffer (get-buffer-create "*pinboard bookmarks*")
      (let ((inhibit-read-only t))
        (erase-buffer)
        (save-excursion
          (dolist (bmk bmks)
            (insert (pinboard-bmk-title bmk) "\n")
            (insert-text-button
             (pinboard-bmk-url bmk)
             'type 'pinboard-url
             'pinboard-url (pinboard-bmk-url bmk))
            (insert "\n"
                    (pinboard-bmk-tag-string bmk) "\n"
                    (pinboard-bmk-annotation bmk)
                    "\n----------------------------------------------------------------------\n")))
        (pinboard-annotations-mode)
        (pop-to-buffer (current-buffer))))))

;;; Marking commands
(defun pinboard-mark-by-title (regexp)
  (interactive
   (list
    (read-regexp "Mark by title (regexp): ")))
  (pinboard--mark-predicate
   (lambda (bmk)
     (string-match-p regexp (pinboard-bmk-title bmk)))))

(defun pinboard-mark-by-url (regexp)
  (interactive
   (list
    (read-regexp "Mark by url (regexp): ")))
  (pinboard--mark-predicate
   (lambda (bmk)
     (string-match-p regexp (pinboard-bmk-url bmk)))))

(defun pinboard-mark-by-tags (tags)
  (interactive
   (list (pinboard--read-tags "Mark by tags: ")))
  (when tags
    (pinboard--mark-predicate
     (lambda (bmk)
       (cl-subsetp tags (pinboard-bmk-tags bmk)
                   :test #'pinboard-case-fold)))))

(defun pinboard--mark-predicate (predicate)
  (let ((count 0))
    (pinboard--do-buffer-lines
     (when (funcall predicate (pinboard-bookmark-at-point))
       (tabulated-list-put-tag ">")
       (incf count)))
    (message "Marked %d bookmark(s)" count)))

;;; Jump
(defun pinboard-jump-to-bookmark (title)
  (interactive
   (list
    (let ((titles
           (mapcar #'pinboard-bmk-title (pinboard-displayed-bookmarks))))
      (completing-read "Jump to bookmark: " titles nil t))))
  (pinboard--goto-line-where
   (lambda ()
     (string= title
              (pinboard-bmk-title (pinboard-bookmark-at-point))))))


;;;; Reading tags
(defvar pinboard--read-tags-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map minibuffer-local-map)
    (define-key map (kbd "TAB") #'completion-at-point)
    map))

(defun pinboard--read-tags (prompt &optional tags)
  (let ((tags-completion-table
         (or tags pinboard-tags))
        (post-completion
         (lambda (_ status)
                     (when (eq status 'finished)
                       (insert " ")))))
    (minibuffer-with-setup-hook
        (lambda ()
          (add-hook 'completion-at-point-functions
                    (lambda ()
                      (pcase (bounds-of-thing-at-point 'symbol)
                        (`(,start . ,end)
                          (list start end tags-completion-table
                                :exit-function post-completion))
                        (_ nil)))
                    nil t))
      (split-string (read-from-minibuffer prompt nil pinboard--read-tags-map)))))


;;;; Bookmark details list
(defvar pinboard-annotations-mode-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map (make-composed-keymap button-buffer-map special-mode-map))))
(define-derived-mode pinboard-annotations-mode special-mode "Pinboard annotations")
(define-key pinboard-annotations-mode-map (kbd "RET") 'find-file-at-point)

(define-button-type 'pinboard-url
    'follow-link t
    'action #'pinboard-browse-url-action)

(defun pinboard-browse-url-action (button)
  (browse-url (button-get button 'pinboard-url)))


;;;; Bookmark popup/editing

(defvar pinboard-edit-template
  "# Edit bookmark title and annotation below.
# The first line is the title, remaining lines are the annotation.
# Lines beginning with a `#' character will be removed.
# Use C-c C-c to save changes or C-c C-k to cancel.
")

(defvar-local pinboard-edited-bookmark nil)

(define-derived-mode pinboard-edit-mode text-mode "Pinboard bookmark")
(define-key pinboard-edit-mode-map (kbd "C-c C-c") #'pinboard-save-edited-bookmark)
(define-key pinboard-edit-mode-map (kbd "C-c C-k") #'pinboard-quit-window)

(define-derived-mode pinboard-view-mode special-mode "Pinboard bookmark")
(define-key pinboard-view-mode-map (kbd "C-c C-k") #'pinboard-quit-window)
(define-key pinboard-view-mode-map (kbd "C-x C-q") #'pinboard-switch-to-edit-mode)

(defun pinboard--popup-bookmark (edit-mode)
  (let ((bmk (pinboard-bookmark-at-point)))
    (with-current-buffer
        (if edit-mode
            (generate-new-buffer "*pinboard bookmark*")
          (get-buffer-create "*pinboard bookmark*"))
      (let ((inhibit-read-only t))
        (erase-buffer)
        (when edit-mode
            (insert pinboard-edit-template))
        (save-excursion
          (insert (pinboard-bmk-title bmk)
                  "\n"
                  (pinboard-bmk-tag-string bmk)
                  "\n"
                  (pinboard-bmk-annotation bmk)
                  "\n"))
        (if edit-mode
            (pinboard-edit-mode)
          (pinboard-view-mode)))
      (setq pinboard-edited-bookmark bmk)
      (pop-to-buffer (current-buffer)))))

(defun pinboard-switch-to-edit-mode ()
  (interactive)
  (message "Use C-c C-c to save changes, C-c C-k to exit.")
  (setq buffer-read-only nil)
  (let ((bmk pinboard-edited-bookmark))
    (pinboard-edit-mode)
    (setq pinboard-edited-bookmark bmk)))

(defun pinboard-save-edited-bookmark ()
  (interactive)
  (let ((bmk pinboard-edited-bookmark)
        (contents (buffer-string)))
    (with-temp-buffer
      (insert contents)
      (goto-char (point-min))
      (save-excursion
        (while (not (eobp))
          (if (looking-at "#")
              (kill-line 1)
            (forward-line))))
      (when (< (count-lines (point-min) (point-max)) 2)
        (error "Title and tags line are required"))
      (let ((title (buffer-substring (point-at-bol) (point-at-eol)))
            (tags (split-string
                   (buffer-substring (point-at-bol 2) (point-at-eol 2))))
            (annotation
             (pinboard-string-trim
              (buffer-substring (point-at-bol 3) (point-max)))))
        (let ((updated (copy-pinboard-bmk bmk))
              (window (selected-window)))
          (setf (pinboard-bmk-title updated) title)
          (setf (pinboard-bmk-tags updated) tags)
          (setf (pinboard-bmk-annotation updated) annotation)
          (if (equal bmk updated)
              (progn
                (message "No changes!")
                (quit-window t window))
            (pinboard--update-bookmark
             updated t
             (lambda (success)
               (when success
                 (message "Updated bookmark")
                 (quit-window t window)
                 (pinboard--redraw-bookmark-list))))))))))

(defun pinboard-quit-window ()
  (interactive)
  (quit-window t))


;;;; Tags list

(defvar pinboard-tag-list-format
  [("#" 10
        pinboard--sort-tag-numeric
        :right-align t)
   ("Tag" 40 t)])

(cl-defstruct (pinboard-tag-entry (:type vector))
  count
  name)

(defvar pinboard-tags-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "RET") 'pinboard-tag-follow)
    (define-key map (kbd "r") 'pinboard-rename-tag)
    (define-key map (kbd "x") 'pinboard-do-flagged-delete-tags)
    (define-key map "j" #'pinboard-jump-to-tag)
    map))

(define-derived-mode pinboard-tags-mode pinboard-tabulated-list-mode
  "Pinboard-tags"
  "Major mode for viewing and editing a list of Pinboard tags.

Commands:
\\[pinboard-tag-follow] -- show bookmarks with this tag in another buffer
\\[pinboard-jump-to-tag] -- move point to line containing a tag by name
\\[pinboard-rename-tag] -- rename a tag, or merge with another
\\[pinboard-mark-for-deletion] -- mark tag at point for deletion
\\[pinboard-do-flagged-delete-tags] -- permanently delete tags marked for deletion"
  (setq tabulated-list-format pinboard-tag-list-format)
  (setq tabulated-list-sort-key '("#" . t))
  (setq tabulated-list-padding 1)
  (setq tabulated-list-entries #'pinboard--tag-tabulated-list-entries)
  (add-hook 'tabulated-list-revert-hook #'pinboard--refresh-tags nil t)
  (tabulated-list-init-header))

;;;###autoload
(defun pinboard-list-tags ()
  (interactive)
  (pinboard-maybe-login)
  (pinboard-fetch-tags t 'ignore)
  (with-current-buffer (get-buffer-create "*pinboard tags*")
    (let ((inhibit-read-only t))
      (erase-buffer)
      (pinboard-tags-mode))
    (setq tabulated-list-entries 'pinboard--tag-tabulated-list-entries)
    (tabulated-list-print)
    (pop-to-buffer (current-buffer))))

(defun pinboard--tag-at-point () (tabulated-list-get-id))

(defun pinboard--tag-tabulated-list-entries ()
  (cl-loop for name being the hash-keys of pinboard-tags
           using (hash-values count)
           collect
           `(,name
             [,(number-to-string count) ,name])))

(defun pinboard--refresh-tags ()
  (let ((progress (make-progress-reporter "Reverting tags...")))
    (pinboard-fetch-tags t 'ignore)
    (progress-reporter-done progress)))

(defun pinboard--sort-tag-numeric (a b)
  (let ((an (gethash (elt a 0) pinboard-tags))
        (bn (gethash (elt b 0) pinboard-tags)))
    (< an bn)))

(defun pinboard-tag-follow (tag)
  "List bookmarks tagged with TAG in another buffer.

Interactively, in a `pinboard-list-tags' buffer, lists bookmarks
with the tag at point."
  (interactive (list (pinboard--tag-at-point)))
  (message "Displaying bookmarks tagged `%s'" tag)
  (pinboard-list-bookmarks-filtered (list tag)))

;; FIXME: Rename multiple tags at once
(defun pinboard-rename-tag ()
  "Rename tag at point."
  (interactive)
  (catch 'cancel
    (let* ((old (pinboard--tag-at-point))
           (new
            (read-string
             (format "Rename tag `%s' to: " old)))
           (merging (gethash new pinboard-tags)))
      (when merging
        (unless (y-or-n-p
                 (format "Merge tag `%s' into `%s'?"
                         old new))
          (message "Canceled merging tags")
          (throw 'cancel t)))
      (pinboard-request
       "tags/rename" `((old ,old) (new ,new))
       t
       (lambda (_)
         (message (if merging
                      "Merged `%s' into `%s'"
                    "Renamed `%s' to `%s'")
                  old new)
         (pinboard--redraw-tags-list))))))

(defun pinboard-do-flagged-delete-tags ()
  "Permanently delete tags marked for deletion."
  (interactive)
  (let* ((tags (pinboard--marked-ids ?D))
         (count (length tags))
         (prompt
          (if (> count 1)
              (format "Permanently delete %d tags?" count)
            (format "Permanently delete tag `%s'?" (first tags)))))
    (if (yes-or-no-p prompt)
        (let ((successes 0) (failures 0))
          (dolist (tag tags)
            (message "Deleting tag `%s'" tag)
            (pinboard--enqueue-request
             "tags/delete" `((tag ,tag))
             (lambda (success)
               (if success
                   (progn
                     (incf successes)
                     (remhash tag pinboard-tags))
                 (incf failures)))))
          (pinboard--enqueue-callback
           (lambda ()
             (message "Deleted %d tag(s), %d error(s)"
                      successes failures)
             (pinboard--redraw-tags-list)))))))

(defun pinboard-jump-to-tag (tag)
  "Read a tag name in minibuffer and move point to its line."
  (interactive
   (list
    (completing-read "Jump to tag: " pinboard-tags nil t)))
  (pinboard--goto-line-where
   (lambda () (string= (pinboard--tag-at-point) tag))))

(defun pinboard--redraw-tags-list ()
  (with-current-buffer "*pinboard tags*"
    (pinboard--with-saved-marks
     (tabulated-list-revert t))))

(provide 'pinboard-list)

;;; pinboard-list.el ends here
