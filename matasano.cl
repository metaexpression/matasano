(proclaim '(optimize (speed 0) (safety 3) (debug 3) (space 0)))
(ql:quickload '(alexandria ironclad iterate anaphora s-base64 cl-ppcre) :silent t)

(defpackage matasano (:use cl alexandria iterate anaphora s-base64 cl-ppcre))

(in-package matasano)

(defun hex-to-octet (str)
	(let ((octets (make-array (/ (length str) 2) :element-type 'unsigned-byte)))
			(iter (for i index-of-vector str)
					(when (evenp i)
							(setf (aref octets (/ i 2))
									(parse-integer str :start i :end (+ 2 i) :radix 16))))
			octets))

(defun octet-to-hex (oct)
	(reduce #'(lambda (x y) (concatenate 'string x y)) 
		(map 'list #'(lambda (x) (format nil "~2,'0x" x)) oct) 
		:initial-value ""))

(defun octet-to-b64 (oct)
	(with-output-to-string (out)
		(encode-base64-bytes oct out)))

(defun b64-to-octet (b64)
	(with-input-from-string (in b64)
		(decode-base64-bytes in)))

(defun octet-to-string (octet)
	(map 'string #'code-char octet))

(defun hex-to-string (hex)
	(octet-to-string (hex-to-octet hex)))

(defun hex-to-base64 (str)
	(octet-to-b64 (hex-to-octet str)))

(defun str-to-octet (str)
	(map 'vector #'char-code str))

(defun xor-octets (oct1 oct2)
	(map 'vector #'logxor oct1 oct2))

(defparameter *frequencies* 
	'(0.08167 0.01492 0.02782 0.04253 0.12702 0.02228 0.02015 0.06094 0.06966 0.00153 0.00772 0.04025 0.02406
	  0.06749 0.07507 0.01929 0.00095 0.05987 0.06327 0.09056 0.02758 0.00978 0.02360 0.00150 0.01974 0.00074))

(defparameter *letter-frequencies* 
	(iter (for i from 97 to 122)
			(collect (list i (elt *frequencies* (- i 97))))))

(defun write-table (table)
	(iter (for (k v) in-hashtable table)
			(collect (list k v))))

(defun read-table (alist)
	(let ((ht (make-hash-table :test #'equalp)))
			(iter (for (k v) in alist)
					(setf (gethash k ht) v))
			ht))

(defun make-frequency-table (list)
	(let ((freq (make-hash-table :test #'equalp)))
			(iter (for x in-sequence list)
					(setf (gethash x freq) (+ 1 (gethash x freq 0))))
			freq))

(defun relative-frequency (table)
	(let* ((entries (write-table table))
		    (sum (reduce #'+ entries :key #'cadr))
		    (rfreq (make-hash-table :test #'equalp)))
			 (iter (for i in entries)
					 (setf (gethash (car i) rfreq)
							 (/ (cadr i) sum)))
		rfreq))

(defun in-range? (val min max)
	(and (>= val min) (<= val max)))

(defun letter? (char)
	(or (in-range? char 65 90) (in-range? char 97 122)))

(defun special-chars? (oct)
	(iter (for c in-sequence oct)
			(if (or (in-range? c 0 9) (in-range? c 14 31) (in-range? c 127 255))
				 (return t))))

(defun oct-downcase (oct)
	(map 'vector (lambda (x) (if (in-range? x 65 90) (+ x 32) x)) oct))

;; scores text for similarity to english on character frequency
(defun score-text (oct)
	(when (special-chars? oct) (return-from score-text 1000))
	(setf oct (oct-downcase (remove-if-not #'letter? oct)))
	(let* ((score 0.0)
			 (english (read-table *letter-frequencies*))
			 (test-frequency (relative-frequency (make-frequency-table oct))))
			 (iter (for i from 97 to 122)
					 (setf score (+ score (abs (- (gethash i test-frequency 0) (gethash i english))))))
		score))

(defun xor-decrypt (ciphertext pass)
	(iter (for i index-of-vector ciphertext)
			(collect (boole boole-xor (aref ciphertext i)
								 			  (elt pass (mod i (length pass)))))))

;; decrypted text, score 
(defun break-xor (oct)
	(iter (for x from 0 to 255)
			(for trial = (xor-decrypt oct (vector x)))
			(finding (list trial (score-text trial) x) 
			 minimizing (score-text trial))))

(defun break-xor-from-list (list)
	(iter (for o in list)
			(for (trial score z) = (break-xor o))
			;; (print (list (octet-to-string (remove-if-not #'letter? trial)) score))
			(finding (list trial score) minimizing score)))

(defun get-bin (n)
	(map 'list (lambda (x) (parse-integer (string x))) (format nil "~b" n)))

(defun hamming-dist (n1 n2)
	(reduce #'+ (get-bin (boole boole-xor n1 n2))))

(defun str-hamming-dist (str1 str2)
	(reduce #'+ (map 'list #'hamming-dist
		(map 'list #'char-code str1) (map 'list #'char-code str2))))

(defun octet-hamming-dist (oct1 oct2)
	(reduce #'+ (map 'list #'hamming-dist oct1 oct2)))

(defun split-by-step (seq step)
	(iter (for i from step to (length seq) by step)
			(for j previous i initially 0)
			(collect (subseq seq j i))))

(defun keysize-score (oct keysize)
	(let ((blocks (split-by-step oct keysize))) 
			(/ (iter (for i from 1 below (length blocks) by 2)
					   (for j from 0 below (length blocks) by 2)
					   (sum (/ (octet-hamming-dist (elt blocks i) (elt blocks j)) keysize)))
				(length blocks))))

(defun find-key-size (oct &key (limit 40))
	(iter (for trial-key from 2 to limit)
			(format t "~a ~8$~%" trial-key (keysize-score oct trial-key))
			(finding trial-key minimizing (keysize-score oct trial-key))))

(defun every-n (seq n offset)
	(map 'vector (lambda (x) x)
		(iter (for i from offset below (length seq) by n)
				(collect (aref seq i)))))

(defun range (min max)
	(iter (for n from min to max)
			(collect n)))

(defun ribbonize-blocks (ciphertext keysize)
	(map 'list (lambda (x) (every-n ciphertext keysize x))
		  (range 0 (- keysize 1))))

(defun collect-xor-key-values (sets)
	(map 'vector (lambda (x) x)
		(iter (for o in sets)
			 (for (text score x) = (break-xor o))
			 ;; (print (list 'debug 2 text score x))
			 (collect x))))

(defun octet-to-byte-array (oct)
	(ironclad:ascii-string-to-byte-array (octet-to-string oct)))

(defun aes-ecb-decrypt (ciphertext key)
	(setf ciphertext (octet-to-byte-array ciphertext))
	(let ((cipher (ironclad:make-cipher :AES :mode :ECB :key (octet-to-byte-array key)))
			(plaintext (make-array (length ciphertext) :element-type '(unsigned-byte 8))))
			(ironclad:decrypt cipher ciphertext plaintext)
			plaintext))

(defun repeated-n-blocks (n octets)
	(let* ((blocks (split-by-step octets n))
			 (table (make-frequency-table blocks))
			 (list (map 'vector #'cadr (write-table table))))
			 (reduce (lambda (x y) (- 1 (+ x y))) list :initial-value 0)))

(defun find-ecb-aes (n list)
	(iter (for i in list)
			(print (repeated-n-blocks n i))
			(finding i maximizing (repeated-n-blocks n i))))

(defun matasano-1 ()
	(octet-to-b64 (hex-to-octet (read-line))))

(defun matasano-2 ()
	(octet-to-hex (xor-octets (hex-to-octet (read-line)) (hex-to-octet (read-line)))))

(defun matasano-3 ()
	(octet-to-string (car (break-xor (hex-to-octet (read-line))))))

(defun matasano-4 ()
	(octet-to-string
		(car
			(break-xor-from-list
		  	(map 'list #'hex-to-octet 
				 (split "\\n" (read-file-into-string "4.txt")))))))

(defvar *plaintext-1* (str-to-octet (format nil "Burning 'em, if you ain't quick and nimble~%I go crazy when I hear a cymbal")))

(defun matasano-5 ()
	(octet-to-hex (xor-decrypt *plaintext-1* (str-to-octet "ICE"))))

(defun matasano-6 ()
	(let* ((raw (b64-to-octet (read-file-into-string "6.txt")))
			 (sets (ribbonize-blocks raw (find-key-size raw)))
			 (key (collect-xor-key-values sets)))
			 (list (octet-to-string key) (octet-to-string (xor-decrypt raw key)))))

(defun matasano-7 ()
	(let* ((data (b64-to-octet (read-file-into-string "7.txt"))))
			 (octet-to-string (aes-ecb-decrypt data (str-to-octet "YELLOW SUBMARINE")))))

(defun matasano-8 ()
	(let* ((data (mapcar #'hex-to-octet (split "\\n" (read-file-into-string "8.txt")))))
			 (octet-to-hex (find-ecb-aes 16 data))))

(defun pkcs-pad (octet block-length)
	(let ((extra-length (mod (length octet) block-length)))
			(if (not (zerop extra-length)) (setf extra-length (- block-length extra-length)))
			(iter (repeat extra-length)
					(setf octet (concatenate 'vector octet (make-array 1 :initial-element 4))))
			octet))

(defun validate-and-strip-pkcs (str)
	(setf str
		(subseq str 0 
			(iter (for x downfrom (- (length str) 1))
				   (if (not (equalp (aref str x) (code-char 4))) (leave (+ x 1)))))))

(defun aes-ecb-encrypt (plaintext key blocksize)
	(setf plaintext (octet-to-byte-array (pkcs-pad plaintext blocksize)))
	(let ((cipher (ironclad:make-cipher :AES :mode :ECB :key (octet-to-byte-array key)))
			(ciphertext (make-array (length plaintext) :element-type '(unsigned-byte 8))))
			(ironclad:encrypt cipher plaintext ciphertext)
			ciphertext))

(defun aes-cbc-encrypt (plaintext key iv blocksize)
	(iter (for x in (split-by-step plaintext blocksize))
			(with acc = iv)
			(setf acc (xor-octets acc x))
			(for res = (aes-ecb-encrypt acc key blocksize))
			(collect res into sets)
			(setf acc res)
			(finally (return (reduce (lambda (x y) (concatenate 'vector x y)) sets)))))

(defun aes-cbc-decrypt (ciphertext key iv blocksize)
	(iter (for x in (split-by-step ciphertext blocksize))
			(with acc = iv)
			(for res = (aes-ecb-decrypt x key))
			(collect (xor-octets res acc) into sets)
			(setf acc x)
			(finally (return (reduce (lambda (x y) (concatenate 'vector x y)) sets)))))

(defun solid-vector (a b) (map 'vector (lambda (x) x) (iter (repeat a) (collect b))))

(defun matasano-10 ()
	(let* ((data (b64-to-octet (read-file-into-string "10.txt"))))
			 (print (length data))
			 (aes-cbc-decrypt data (str-to-octet "YELLOW SUBMARINE") (solid-vector 16 0) 16)))

(defun gen-random-key (n)
	(map 'vector (lambda (x) x) (iter (repeat n) (collect (random 256)))))

(defun random-padding (oct)
	(concatenate 'vector (gen-random-key (+ 5 (random 5))) oct (gen-random-key (+ 5 (random 5)))))

(defun aes-oracle (plaintext)
	(let ((thing (random 2)))
		(if (eql thing 1)
			 (aes-cbc-encrypt (random-padding plaintext) (gen-random-key 16) (gen-random-key 16) 16)
			 (aes-ecb-encrypt (random-padding plaintext) (gen-random-key 16) 16))))

(defun detect-cipher-mode (oracle n)
	(let ((res (funcall oracle (solid-vector (* n 4) #xaa))))
			(if (> (repeated-n-blocks n res) 0) :ecb :cbc)))

(defparameter *hidden-string* 
  "Um9sbGluJyBpbiBteSA1LjAKV2l0aCBteSByYWctdG9wIGRvd24gc28gbXkg
	aGFpciBjYW4gYmxvdwpUaGUgZ2lybGllcyBvbiBzdGFuZGJ5IHdhdmluZyBq
	dXN0IHRvIHNheSBoaQpEaWQgeW91IHN0b3A/IE5vLCBJIGp1c3QgZHJvdmUg
	YnkK")

(defparameter *matasano-12-key* (gen-random-key 16))

(defun matasano-12-oracle (string)
	(aes-ecb-encrypt (concatenate 'vector string (b64-to-octet *hidden-string*)) *matasano-12-key* 16))

(defun find-block-size (oracle)
	(iter (for x upfrom 1)
			(for y = (solid-vector x #xaa))
		   (for last-length = (length (funcall oracle y)))
			(for length = (length (funcall oracle (solid-vector (+ x 1) #xaa))))
			(aif (> length last-length) (leave (- length last-length)))))

(defun get-block (index size seq)
	(nth index 
		(iter (for x from 0 below (length seq) by size)
				(for y from size below (length seq) by size)
				(collect (subseq seq x y)))))

(defun matasano-12 (bytes-to-decrypt)
	(let ((block-size (find-block-size #'matasano-12-oracle))
			(decrypted-bytes nil))
			(when (eql (detect-cipher-mode #'matasano-12-oracle 16) :cbc)
					(error "oracle not using ecb!"))
			;; the first block has to be handled with padding, instead of using decoded bytes
			(iter (for b from 0 below block-size)
					(for c from 0 below bytes-to-decrypt) ;; if bytes-to-decrypt is below block-size
					(for l downfrom (- block-size 1))
					(with decoded-string = #())
					(for v = (solid-vector l #xaa))
					(for result = (get-block 0 block-size (funcall #'matasano-12-oracle v)))
					(let ((table (make-hash-table :test #'equalp)))
							(iter (for x from 0 to 255)
									(let ((trial-block
												(get-block 0 block-size
													(funcall #'matasano-12-oracle 
													(concatenate 'vector v decoded-string (vector x))))))
											(setf (gethash trial-block table) x)))
							(setf decoded-string
								(concatenate 'vector decoded-string (vector (gethash result table)))))
					(finally (setf decrypted-bytes decoded-string)))
			(iter (for byte-to-decrypt from block-size below bytes-to-decrypt)
					(for target-block-index = (floor (/ byte-to-decrypt block-size)))
					(for padding = 
						(solid-vector 
							(- (- block-size 1) (mod byte-to-decrypt block-size)) #xaa))
					(for target-block = 
						(get-block target-block-index block-size 
							(funcall #'matasano-12-oracle padding)))
					(iter (for x from 0 to 255)
							(with trials = (make-hash-table :test #'equalp))
							(with known-info = 
								(subseq decrypted-bytes (- (length decrypted-bytes) (- block-size 1))))
							;; populate that motherfucker
							(for raw-block = (concatenate 'vector known-info (vector x)))
							(for trial-block = 
								(get-block 0 block-size (funcall #'matasano-12-oracle raw-block)))
							(setf (gethash trial-block trials) x)
							(finally (setf decrypted-bytes 
												(concatenate 'vector decrypted-bytes 
													(vector (gethash target-block trials)))))))
			(coerce (map 'vector #'code-char decrypted-bytes) 'string)))

(defun convert-kv (str)
	(iter (for x in (split "&" str))
			(let ((zoz (split "=" x)))
					(collect zoz))))

(defun user-profile (email)
	(format nil "email=~a&uid=10&role=user" (regex-replace-all "[&=]" email "")))

(defconstant matasano-13-key (gen-random-key 16))

(defun matasano-13-oracle (email)
	(aes-ecb-encrypt (str-to-octet (user-profile email)) matasano-13-key 16))

(defun matasano-13-verifier (ciphertext)
	(let ((plaintext (validate-and-strip-pkcs (octet-to-string (aes-ecb-decrypt ciphertext matasano-13-key)))))
			(print plaintext)
			(convert-kv plaintext)))

(defun matasano-13 ()
	(let ((ciphertext1 (matasano-13-oracle "arathnim!@xyz"))
			(ciphertext2 (matasano-13-oracle (octet-to-string (concatenate 'vector (solid-vector 10 65) 
																										  (str-to-octet "admin")
																										  (solid-vector 11 #x04))))))
			(matasano-13-verifier ciphertext1)
			;; to complete, just graft the second block of ciphertext2 onto the third block of ciphertext1
			(iter (for x in-vector (get-block 1 16 ciphertext2))
					(for y from (* 2 16) below (* 3 16))
					(setf (aref ciphertext1 y) x))
			(matasano-13-verifier ciphertext1)))

(defparameter *matasano-14-key* (gen-random-key 16))

(defun matasano-14-oracle (string)
	(aes-ecb-encrypt 
		(concatenate 'vector 
			(map 'vector (lambda (x) x) (iter (repeat (random 50)) (collect (random 250)))) 
			string 
			(b64-to-octet *hidden-string*)) 
		*matasano-14-key* 16))
