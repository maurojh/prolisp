(defpackage :mini (:use :cl)
	    (:export :wam :exec))

(in-package :mini)

(declaim (optimize (speed 3) (debug 0) (safety 0) (space 0))
	 (ftype (function (* *) t) bindte)
         (ftype (function (*) t) reduce-infix)
         (ftype (function (* * *) t) reduce-matching-op)
         (ftype (function () t) read_prompt)
	 (ftype (function () t) banner)
         (ftype (function (&optional *) t) rchnsep)
         (ftype (function (&optional *) t) read_code_tail)
	 (ftype (function (*) t) readProvePrintLoop)
	 (ftype (function (* &optional *) t) read_args)
	 (ftype (function (* &optional *) t) xread_args)
	 (ftype (function (* &optional *) t) read_term)
	 (ftype (function (* &optional *) t) xread_term)
	 (ftype (function (* &optional *) t) read_pred)
	 (ftype (function (* *) t) ultimate)
	 (ftype (function (*) t) vvarp)
	 (ftype (function (* *) t) cop)
	 (ftype (function (*) t) pr_det)
	 (ftype (function (*) t) genvar)
	 (ftype (function (*) t) ult)
	 (ftype (function () t) load_pc)
	 (ftype (function () t) cont_eval)
	 (ftype (function () t) load_A2)
	 (ftype (function (*) t) shallow_backtrack)
	 (ftype (function () t) backtrack)
	 (ftype (function (*) t) pr_choice)
	 (ftype (function (*) t) pr)
	 (ftype (function (*) t) pr2)
	 (ftype (function (*) t) lisploop)
	 (ftype (function (* *) t) unif)
         (ftype (function (*) t) impl)
         (ftype (function (*) t) expl)
	 (ftype (function () t) printvar)
	 (ftype (function (* *) t) writesl)
	 (ftype (function (* *) t) writesf)
         (ftype (function (*) t) write1)
	 (ftype (function () t) read_terme)
	 (ftype (function (*) t) write1))

;; A solution to prefix conversion:
(defparameter *infix-ops* 
  '((([ list match ]) ({ elts match }) (|(| nil match |)|))
    ((not not unary) (~ |neg| unary) )
    ((*) (/))
    ((+) (-))
    ((<) (>) (<=) (>=) (=) (/=))
    ((and) (& and) (^ and))
    ((or) (\| or))
    ((=>))
    ((<=>))
    ((|,|)))
  "A list of lists of operators, highest precedence first.")

(defun length>1(x) (> (length x) 1))

(defun replace-subseq (sequence start length new)
  (nconc (subseq sequence 0 start) (list new)
         (subseq sequence (+ start length))))

(defun op-token (op) (first op))
(defun op-name (op) (or (second op) (first op)))
(defun op-type (op) (or (third op) 'BINARY))
(defun op-match (op) (fourth op))
(defun length=1(s) (= (length s) 1))

(defun ->prefix (infix)
  "Convert an infix expression to prefix."
  (loop 
     (when (not (length>1 infix))
       (RETURN (first infix)))
     (setf infix (reduce-infix infix))))

(defun change_infix (s)
  (cond ((null s) s)
	((null (cdr s)) s)
	((and (eq (car s) '|(|)
	      (eq (cadr s) '-))
	(cons '|(| (cons '\~ (change_infix (cddr s)))))
	((and (eq (car s) '*)
	      (eq (cadr s) '-))
	 (cons '* (cons '\~ (change_infix (cddr s)))))
        ((and (eq (car s) '/)
	      (eq (cadr s) '-))
	 (cons '/ (cons '\~ (change_infix (cddr s)))))
	(t (cons (car s) (change_infix (cdr s ))))  ))

(defun prefx(s) (list (->prefix
		       (change_infix
			(if (and (consp s)
				(eq (car s) '-))
			   (cons '~ (cdr s))
			   s))) ))

(defun reduce-infix (infix)
  "Find and reduce the highest-precedence operator."
  (dolist (ops *infix-ops*
     (error "Bad syntax for infix expression: ~S" infix))
     (let* ((pos (position-if 
              #'(lambda (i) (assoc i ops)) infix
                :from-end (eq (op-type (first ops))
                'MATCH)))
              (op (when pos (assoc (elt infix pos) ops))))
        (when pos
         (RETURN (case (op-type op)
           (MATCH (reduce-matching-op op pos infix))
           (UNARY (replace-subseq infix pos 2 
                   (list (cons (op-name op) 1)
                         (elt infix (+ pos 1)))))
           (BINARY (replace-subseq infix (- pos 1) 3
                   (list (cons (op-name op) 2)
                         (elt infix (- pos 1)) 
                         (elt infix (+ pos 1)))))))))))
(defun op(s) (car s))
(defun arg1(s) (cadr s))
(defun arg2(s) (caddr s))

(defun remove-commas (exp)
  "Convert (|,| a b) to (a b)."
  (cond ((eq (op exp) '|,|)
         (nconc (remove-commas (arg1 exp) )
                (remove-commas (arg2 exp))))
        (t (list exp))))

(defun handle-quantifiers(x) x)
(defun function-symbol? (x) 
  (and (symbolp x) (not (member x '(and or not ||)))
       (alphanumericp (char (string x) 0))))

(defun reduce-matching-op (op pos infix)
  "Find the matching op (paren or bracket) and reduce."
  ;; Note we don't worry about nested parens because we search :from-end
  (let* ((end (position (op-match op) infix :start pos))
         (len (+ 1 (- end pos)))
         (inside-parens (remove-commas
			 (->prefix (subseq infix (+ pos 1) end)))))
    (cond ((not (eq (op-name op) '|(|)) ;; handle {a,b} or [a,b]
           (replace-subseq infix pos len 
                           (cons (op-name op) inside-parens))) ; {set}
          ((and (> pos 0)  ;; handle f(a,b)
                (function-symbol? (elt infix (- pos 1))))
           (handle-quantifiers
            (replace-subseq infix (- pos 1) (+ len 1)
			    (cons (elt infix (- pos 1))
				  inside-parens))))
          (t (replace-subseq infix pos len
			   (first inside-parens))))))

;; mini-Wam
;; boot
;;

(defparameter *keep-going* nil)

(defun exec(str)
  (setf *keep-going* nil)
  (in-package :mini)
  (let ( (oldin *standard-input*)
	(oldout *standard-output*)
        (fstr(make-array '(0) :element-type 'base-char
			 :fill-pointer 0 :adjustable t)))
    (with-input-from-string (s (format nil "~a " str))
      (setf *standard-input* s)
      (with-output-to-string
	  (z fstr)
	(setf *standard-output* z)
      (handler-case (lisploop (read_code_tail))
	  (error(e) (format t "toplevel error: ~a~%" e)  ))))
      (setf *standard-input* oldin
	    *standard-output* oldout)
       (in-package :cl-user) 
      fstr))

(defun wam ()
  (setf *keep-going* t)
  (banner)
  (in-package :mini)
  (readProvePrintLoop (read_prompt))
  (in-package :cl-user))

(defun read_prompt () 
  (terpri)
  (format t "| ?- ")
  (finish-output)
  (read_code_tail))

(defun banner ()
  (dotimes (i 2) (terpri))
  (format t "mini-Wam~%")
  (dotimes (i 2) (terpri)))

(defun l ()
  (format t "Back to mini-Wam top-level~%")
  (readProvePrintLoop (read_prompt)))


;; mini-wam
;; reader

(defvar *lvar nil)
(set-macro-character #\% (get-macro-character #\;))

(defun rch (&optional (stream *standard-input*))
  (do ((ch (read-char stream) (read-char stream)))
      ((char/= ch #\Newline) ch)))

(defun ignore-to-eol(xch &optional (stream *standard-input*))
  (do ((ch xch (read-char stream)))
      ((char= ch #\Newline) (rchnsep stream))))	       
       
(defun commts(ch &optional (stream *standard-input*))
  (if (char= #\% ch) (ignore-to-eol (read-char  stream) stream)
      ch))

(defun rchnsep (&optional (stream *standard-input*))	
  (do ((ch (rch stream) (rch stream)))
      ( (and (char/= ch #\space)
	     (char/= ch #\tab)) (commts ch stream)  ) ))

(defun spcial (ch) (char= ch #\_))
(defun alphanum (ch) (or (alphanumericp ch)
			 (spcial ch)))
(defun valdigit (ch) (digit-char-p ch)) 


(defun read_frac(ch x acc &optional (stream *standard-input*))
  (cond((digit-char-p (peek-char nil stream))
	(read_frac (read-char stream)
		   (/ x 10.0)
		   (+ acc (* (valdigit ch) x)  )
		   stream))
       (t (+ acc (* (valdigit ch) x))  )))
	 
(defun read_fr(ch x acc &optional (stream *standard-input*))
  (declare (ignorable ch))
  (if (not (digit-char-p (peek-char nil stream)))
      (progn (unread-char  #\. stream)  0.0)
      (read_frac (read-char stream) x acc stream)))

;; Improvements: Add double precision to numbers
(defun read_number (sign ch &optional (stream *standard-input*)) 
  (do ((v (valdigit ch) (+ (* v 10) (valdigit (read-char stream)))))
      ((not (digit-char-p (peek-char nil stream)))
       (if (char= (peek-char nil stream) #\.)
	   (* sign (+ v  (read_fr (read-char stream)
				  0.1 0.0 stream) ))
           (* v sign))) ))

(defun implode (lch) (intern (map 'string #'identity lch)))

(defun read_atom (ch &optional (stream *standard-input*))
  (cond  ((char= ch #\-)  '-)
         ((char= ch #\*)  '*)
         ((char= ch #\/)  '/)
         ((char= ch #\+)  '+)
	 ((and (char= ch #\<)
	       (char= (peek-char nil stream) #\()) '|lt|)
	 ((and (char= ch #\>)
	       (char= (peek-char nil stream) #\()) '|gt|)
	 ((and (char= ch #\=)
	       (char= (peek-char nil stream) #\()) '|eqn|)
	 ((and (char= ch #\<)
	       (char= (peek-char nil stream) #\=))
	  (read-char stream) '|<=|)
         ((and (char= ch #\>)
	       (char= (peek-char nil stream) #\=))
	     (read-char stream) '|>=|)	 
         (t (do ((lch (list ch) (push (read-char stream) lch)))
		((not (alphanum (peek-char nil stream)))
		 (implode (reverse lch)))  ))))

(defun read_at (ch &optional (stream *standard-input*))
  (do ((lch (list ch) (push (read-char stream) lch)))
      ((char= (peek-char nil stream) #\') (read-char stream)
       (implode (reverse lch)))))

(defun do_l (x) (if (atom x) x
		    (list '(\. . 2)
			  (car x)
			  (do_l (cdr x)))))

(defun read_string (ch &optional (stream *standard-input*))
  (do ((lch (list (char-int ch)) 
            (push (char-int (read-char stream)) lch)))
      ((char= (peek-char nil stream) #\") (read-char stream)
       (do_l (reverse lch)))))

(defun read_var (type_var ch &optional (stream *standard-input*)) 
  (let ((v (read_atom ch stream)))
	(cons type_var
	  (position v 
            (if (member v *lvar)
                *lvar
                 (setq *lvar (append *lvar (list v)))))) ))

(defun read_simple (ch &optional (stream *standard-input*))
  (cond
    ((and (eq ch #\n) (upper-case-p (peek-char nil stream)))
     (read_var 'N (read-char stream) stream))
   ((or (spcial ch) (upper-case-p ch)) (read_var 'V ch stream))
   ((digit-char-p ch) (read_number 1 ch stream))
   ((and (char= ch #\-) (digit-char-p (peek-char nil stream)))
    (read_number -1 (read-char stream) stream ))
   ((char= ch #\") (read_string (read-char stream) stream))
   ((char= ch #\') (read_at (read-char stream) stream))
   ((char= ch #\#) (unread-char ch stream) (read stream))
   (t (read_atom ch stream))))

(defun read_fct (ch &optional (stream *standard-input*))
(let ((fct (read_simple ch stream))
      (c (rchnsep stream)))
    (if (char= c #\()
	(let ((la (read_args (rchnsep stream) stream)))
	  (cons (list fct ) la))
      (progn (unread-char c stream) fct))))
                
(defun read_args (ch &optional (stream *standard-input*)) 
  (let ((arg (read_term ch stream)))
    (if (char= (rchnsep stream) #\,)
	(cons arg (read_args (rchnsep stream) stream))
      (list arg))))

(defun read_factor (ch &optional (stream *standard-input*))
  (cond
   ((or (spcial ch) (upper-case-p ch)) (read_var 'V ch stream))
   ((digit-char-p ch) (read_number 1 ch stream))
   ((char= ch #\") (read_string  (read-char stream) stream))
   ((char= ch #\') (read_at (read-char stream) stream))
   ((char= ch #\#) (unread-char ch stream) (read stream))
   ((char= ch #\() '|(|)
   ((char= ch #\)) '|)|)
   (t (read_atom ch stream))))

(defun read_expr (ch &optional (stream *standard-input*)) 
  (let ((arg (read_factor ch stream)))
    (let ( (next-ch (rchnsep stream)))
    (cond ( (eql next-ch #\,)
	    (list arg) )
          ( (eql next-ch #\.)
	   (unread-char next-ch stream)
	    (list arg))
	  (t (unread-char next-ch stream)
	     (cons arg (read_expr (rchnsep stream) stream)) ))) ))
  
(defparameter *cns* '(\.)) ;;(the fixnum 2)))

(defun read_list (ch &optional (stream *standard-input*))
  (if (char= ch #\])
      ()
    (let ((te (read_term ch stream)))
      (case (rchnsep stream)
	    (#\, (list *cns* te 
                (read_list (rchnsep stream) stream)))
	    (#\| (prog1 (list *cns* te
                 (read_term (rchnsep stream) stream))
		   (rchnsep stream))) 
	    (#\] (list *cns* te nil))))))

(defun read_term (ch &optional (stream *standard-input*))
  (if (char= ch #\[)
      (read_list (rchnsep stream) stream)
      (read_fct ch stream)))

(defun read_tail (ch &optional (stream *standard-input*))
  (let ((tete (read_pred ch stream)))
    (if (equal tete '(|one|))
	(let* ((solvendum (read_pred (rchnsep stream) stream))
	       (chr (rchnsep stream)))
	  (cond ( (char= chr #\.) (list tete solvendum '(|nt|)))
		( (char= chr #\,)
		 (cons tete (cons solvendum
				  (cons '(|nt|)
					(read_tail
					 (rchnsep stream) stream)))))
	        (t (unread-char chr stream)
	           (cons tete (read_tail (rchnsep stream) stream)))))
      (let ((chr (rchnsep stream)))
        (cond ( (char= chr #\.) (list tete))
	    ( (char= chr #\,)
	     (cons tete (read_tail (rchnsep stream) stream)))
	    (t (unread-char chr stream)
	       (cons tete (read_tail (rchnsep stream) stream))))))))

(defun vname(v)
  (cond ((not (vvarp v)) v)
        (t (let ((x (symbol-name v)))
	     (intern (subseq x 1 (length x)))))))

;; Lisp uses uppercase ids, and Prolog uses lowercase.
;; (mkLispID '|fib|) converts |fib| to FIB, where
;; |fib| may be replaced by any Prolog id.
(defun mkLispID(n)
  (intern (string-upcase
		      (symbol-name  n  ))))

;; Read Prolog Deterministica
(defun ximplode (lch) (intern (string-upcase
			       (map 'string #'identity lch) )))
(defun xread_atom (ch &optional (stream *standard-input*)) 
  (do ((lch (list ch) (push (read-char stream) lch)))
      ((not (alphanum (peek-char nil stream)))
       (ximplode (reverse lch)))))

(defun xread_at (ch &optional (stream *standard-input*))
  (do ((lch (list ch) (push (read-char stream) lch)))
      ((char= (peek-char nil stream) #\')
       (read-char stream) (implode (reverse lch)))))

(defun xread_string (ch &optional (stream *standard-input*))
  (do ((lch (list (char-int ch)) (push (char-int (read-char stream)) lch)))
      ((char= (peek-char nil stream) #\") (read-char stream)
       (coerce (reverse lch) 'string))))

(defun xread_simple (ch &optional (stream *standard-input*))
  (cond
   ((digit-char-p ch) (read_number 1 ch stream ))
   ((char= ch #\-) (read_number -1 (read-char stream) stream ))
   ((char= ch #\") (xread_string (read-char stream) stream))
   ((char= ch #\') (xread_at (read-char stream) stream))
   ((char= ch #\#) (unread-char ch stream) (read stream))
   (t (xread_atom ch stream))))

(defun xread_fct (ch &optional (stream *standard-input*))
  (let ((fct (xread_simple ch stream)) (c (rchnsep stream)))
    (if (char= c #\()
	(let ((la (xread_args (rchnsep stream) stream)))
	  (cons (list fct (length la)) la))
      (progn (unread-char c stream) fct))))
                
(defun xread_args (ch &optional (stream *standard-input*)) 
  (let ((arg (xread_term ch stream)))
    (if (char= (rchnsep stream) #\,)
	(cons arg (xread_args (rchnsep stream) stream))
      (list arg))))
   
(defun xread_list (ch &optional (stream *standard-input*))
  (if (char= ch #\])
      ()
    (let ((te (xread_term ch stream)))
      (case (rchnsep stream)
	    (#\, (cons te (xread_list (rchnsep stream) stream)))
	    (#\| (prog1 (cons te (read_term (rchnsep stream) stream))
		   (rchnsep stream))) 
	    (#\] (cons te nil))))))

(defun xread_term (ch &optional (stream *standard-input*))
  (if (char= ch #\[)
      (xread_list (rchnsep stream) stream)
      (xread_fct ch stream))) 

(defun xread_pred (ch &optional (stream *standard-input*)) 
  (let ((nom (xread_atom ch stream)) (c (rchnsep stream)))
    (if (char= c #\()
	(cons nom (xread_args (rchnsep stream) stream)) 
      (progn (unread-char c stream) (list nom)))))

(defun xread_tail (ch &optional (stream *standard-input*))	
  (let ((tete (xread_pred ch stream)))
    (if (char= (rchnsep stream) #\.)
	(list tete)
      (cons tete (xread_tail (rchnsep stream) stream)))))
;;end read Prolog deterministica

;; Tools for Lisp-Prolog communication:

;; (fix xs) converts all ids in a predicate to
;; Lisp ids. For instance, if xs= (|fib| |n| |?f|)
;; to (FIB N ?F).
(defun fix(xs)
  (mapcar #'mkLispID xs ))

(defun sfx(s) (car (last s)))
(defun rmsfx(s) (butlast s))
(defun pfx(s) (car (cdr s)))
(defun rmpfx(s) (cons (car s) (cddr s)))

(defun vvarp(v)
  (and  (symbolp v)
	    (eql (aref (symbol-name v) 0) #\?)))

(defun modedeclarationp(s)
  (cond ((null s) nil)
	((and (consp s) (vvarp (car s))) t)
	(t (modedeclarationp (cdr s))) ))

(defun notStructure(x)
  (not (and (consp x)
	    (not (eq (car x) 'V)))))

(defun hasNoStructure(pred)
  (or (atom pred)
      (eq (car pred) '|is|)
      (every #'notStructure pred)))

(defun onlyLocals(cl)
  (every #'hasNoStructure cl))

(defun changePred(p)
  (cond ((null p) p)
        ((atom p) p)
	((eq (car p) 'V)
	 (cons 'L (changePred (cdr p))))
	(t (cons (changePred (car p)) (changePred (cdr p)))) ))

(defun changeClause(cl)
  (mapcar #'changePred cl))

(defun fixVar(cl)
  (if (onlyLocals cl)
      (changeClause cl)
      cl))

(defun read_clause (ch &optional (stream *standard-input*))
  (let ((tete (read_pred ch stream))
	(neck (rchnsep stream)))
    (if (char= neck #\.)
	(cond (  (modedeclarationp tete)
	         (list 'mdef (fix  tete  )))
	      (t (list tete)))
	(let ((nneck (read-char stream)))
	  (cond (  (and (char= neck #\:) (char= nneck #\-)
			(get (mkLispId (car tete)) 'mod) )
		   (let ((tail (xread_tail (rchnsep stream) stream)))
		     (cons 'def  (cons (fix tete) tail))))
		(t (cons tete
			 (read_tail (rchnsep stream)
				    stream))))  )) ))

(defun processIs(l)
   (cond
    ( (and l   (consp (cdr l))
	       (consp (cadr l))
	       (equal (car (cadr l)) '|is|))
	 (cons (cons '|is|
		      (cons (car l) (cdr (cadr l))))
	       (processIs (cddr l))))
    ( l (cons  (car l) (processIs (cdr l))))))

(defun processCut (l)
  (when l (cons (if (or (eq (caar l) '!)
			(eq (caar l) '|nt|)
			   )
		  `(,(caar l) ,(length *lvar) ,@(cdar l))
		  (car l))
	      (processCut (cdr l)))))

(defun read_code_cl (&optional (stream *standard-input*))
  (let ((*lvar ()))
    (let ((x (read_clause (rchnsep stream) stream)))
      (cond ((member (car x)  '(pdef! pdef sdef! sdef mdef def))  x)
            (t  (cons (length *lvar)
		      (processCut (processIs x))))))))

(defun read_code_tail (&optional (stream *standard-input*))
  (setq *lvar ())
  (let ((x (read_tail (rchnsep stream) stream)))
     (cons (length *lvar) (append (processCut (processIs x))
				 (list '(|true|))))))

(defun listNom(X)
  (cond ( (and (consp X)  (eq (car X) 'V) ) X)
	( (member X '(- + * /)) X)
	(t (list X))))

(defun read_pred (ch &optional (stream *standard-input*)) 
  (let ((nom (read_simple ch stream))
	(c (rchnsep stream)))
    (cond ( (equal nom '|is|)
	    (cons nom (prefx (read_expr c stream) ) ))
          ( (char= c #\() 
            (cons nom (read_args (rchnsep stream) stream)))
	  ( (char= c #\,) (listNom nom))
          (t (unread-char c stream) (listNom nom)))))

(defun rdc(stream)
  (handler-case (read_code_cl stream)
    (error (e) (declare (ignorable e))  nil)))

(defun rd_file(fileName)
  (with-open-file (s fileName)
    (loop for l = (rdc s) then
	 (rdc s)
       while l
       collect l)))

;; Begin Mauro Honorato
	     
;; Aqui comecam os macros que convertem de Prolog deterministica
;; para Lisp. Utilizando a capacidade da Lisp de retornar multiple
;; values para simular as os predicados da Prolog. 
;; Cada clausula eh colocada dentro de um block et. Se algum 
;; predicado falha, temos um return-from et. 
;; Um block et, portanto, faz o papel de um (and p1 p2 p3 ...). 

;; Testa se o predicado eh um operador aritmetico
(defun arithmeticp(p)
  (and (consp p)
	    (member (car p) '(+ - * /))))

;; Identificadores para constantes.
(defun cnsname(c)
  (cond ( (symbolp c) c)
	( (and (consp c) (equal (car c) 'quote))
	  (cadr c))
	((numberp c)
	 (intern (format nil "~a" c))) ))

;; Testa se temos um operador logico
(defun ispred(p)
  (and (consp p)
       (member (car p) '(> < >= <= = eq eql equal))))

(defun apply-mode(xs ys)
  (cond ((and (null xs) (null ys)) nil)
	((null xs) (error "wrong arity: ~a~%" ys))
	((null ys) (error "wrong arity: ~a~%" xs))
	((equal (car xs) (car ys))
	 (cons (car xs) (apply-mode (cdr xs) (cdr ys))))
	((equal (car xs) '-)
	 (cons (car ys) (apply-mode (cdr xs) (cdr ys))))
	((and (equal (car xs) '+)
	      (symbolp (car ys)))
	 (cons (list 'quote (car ys))
	       (apply-mode (cdr xs) (cdr ys))))))
    

;; chain converte Prolog para Lisp. 
(defun chain(hd tail)
  (cond ((null tail) `(values ,@(cdr hd)   ))
	((arithmeticp (car tail))
	 `(multiple-value-bind
	      ,(mapcar #'cnsname (cdr (car tail)))
	      (values (,(car (car tail))
			,@(cddr (car tail)))
		      ,@(cddr (car tail)))
	    (declare (ignorable ,@(mapcar #'cnsname
				       (cdr (car tail)))))
	    ,(chain hd (cdr tail))))
	((ispred (car tail))
	`(progn (when (not ,(car tail)) (return-from et nil))
	   (return-from vel ,(chain hd (cdr tail))   )))
	( (and (consp (car tail))
	       (equal (car (car tail)) 'univ))
	 `(let (( ,(cadr (car tail)) ,(caddr (car tail))))
	    ,(chain hd (cdr tail))))
	((and (consp (car tail))
	      (symbolp (car (car tail)))
	      (get (car (car tail)) 'mod))
	 `(multiple-value-bind
		  ,(mapcar #'cnsname (cdr (car tail)))
	      ,(apply-mode (get (car (car tail)) 'mod)
			   (car tail))
	      (declare (ignorable ,@(mapcar #'cnsname
					    (cdr (car tail)))))
		       ,(chain hd (cdr tail))) ))  )

(defun funChain(hd tail)
  (cond ((null tail)  (cadr hd))
	((arithmeticp (car tail))
	 `(let (( ,(cadr (car tail))
		  ,(cons (car (car tail)) (cddr (car tail)) )))
	          ,(funChain hd (cdr tail))))  
	((ispred (car tail))
	 `(progn (when (not ,(car tail)) (return-from et nil))
		 ,(funChain hd (cdr tail))   ))
	( (and (consp (car tail))
	       (equal (car (car tail)) 'univ))
	 `(let (( ,(cadr (car tail)) ,(caddr (car tail))))
	    ,(funChain hd (cdr tail))))
	((and (consp (car tail))
	      (null (cdr tail))
	      (symbolp (car (car tail)))
	      (get (car (car tail)) 'mod))
	  (cons (car (car tail)) (cddr (car tail)))) 
	((and (consp (car tail))
	      (symbolp (car (car tail)))
	      (get (car (car tail)) 'mod))
	 `(let (( ,(cadr (car tail))
		 ,(cons (car (car tail)) (cddr (car tail)) )))
	        ,(funChain hd (cdr tail))))  ))  

(defun mkFun(clause)
  `(block et ,(funChain (car clause) (cdr clause))))

(defun mkAND(clause)
  `(block et ,(chain (car clause) (cdr clause))))

(defun shw(x)
  (format t "Code= ~a~%" x) x)

;; Funcao check que verifica a ocorrencia
;; de apenas um mais na clausula
(defmacro clauseSetFunctor(s) `(caar ,s))

(defun checkFunMode(m)
  (let (( md (get (clauseSetFunctor m) 'mod)))
  (and (eql (cadr md) '+)
       (every (lambda(x) (eql x '-)) (cddr md)) )))

(defun mkdef(args clauses &optional (funMode (checkFunMode (car clauses))))
   (if funMode
	   (list 'lambda (cdr args)
			 (cons 'or
			      (loop for x in clauses collect	  
				   (mkFun x))))
	   (list 'lambda args
		 `(declare (ignorable ,@args))
		 (cons 'block (cons 'vel
			      (loop for x in clauses collect
				   (mkAnd x)))))) )
  
(defun ck(nm args p clauses)
  (if (and (consp p) (equal args p)
	   (every #'symbolp p))
      clauses
      (error "(def ~a ~a|~a...)?" nm args p)))

(defun getfun(s) (car s))
(defun getargs(s)  (cdr s))

;; macro para converter Prolog deterministica para Lisp.
(defmacro def (&rest clause)
  (let* ((hd (car clause))
	 (fun (getfun hd))
	 (args (getargs hd)))
  (setf (get fun 'clauses)
     `(,@(get fun 'clauses)
	 ,(ck fun (get fun 'vs) args clause )))
  `(setf (symbol-function ',fun)
		 ,(mkdef args (get fun 'clauses)) )))

(defun vmode(v)
  (cond ((vvarp v) '+)
	(t '-)))

(defun argnames(vs)
  (loop for v in vs collect (vname v)))

(defun declaremodes(vs)
  (loop for v in vs collect (vmode v)))

;; Inicializa predicados da Prolog deterministica. 
;; Armazena os modos, argumentos e as clausulas.

(defmacro mdef(hd)
  (let ((fun (getfun hd))
	(args (getargs hd)))
    `(progn (setf (get ',fun 'clauses) nil)
         (setf (get ',fun 'vs) (argnames ',args))
         (setf (get ',fun 'mod) (cons ',fun (declaremodes ',args))))))
;; End Mauro Honorato

;; mini-wam
;; Machine
;; I. Registers
;;

(defconstant BottomG (the fixnum 0))
(defconstant BottomL (the fixnum 500000))
(defconstant +LocalStackOverflow+ (the fixnum 1500000))

;; Mem implements the local stack and the heap.
(defvar Mem (make-array +LocalStackOverflow+
			:initial-element 0 ))

;; The trail stack is implemented in a separate vector.
(defconstant BottomTR (the fixnum 0))
(defconstant +TrailOverflow+ 1000000)
(defvar trailMem
  (make-array +TrailOverflow+ :initial-element 0
	      :element-type 'fixnum))

;; The arguments of a predicate are stored in xArgs.
(defvar xArgs (make-array 50 :initial-element 0))
  
(defvar TR (the fixnum 0)) ;;top of the trail stack
(defvar *LocalPointer*     ;;top of the local stack
  (the fixnum 0)) 
(defvar *GPointer*         ;;top of the copy stack
  (the fixnum 0))
(defvar CP (the fixnum 0))     ;;current continuation
(defvar CL (the fixnum 0))     ;;mother block
(defvar Cut_pt (the fixnum 0)) ;;specific cut
(defvar BL (the fixnum 0))     ;;last choice point
(defvar BG (the fixnum 0))
(defvar PC (the fixnum 0))     ;;current goal
(defvar PCE (the fixnum 0))    ;;current environment
(defvar Duboulot)

;; Environment part of the action block allocation
;; in the local stack:
;; BL field -- previous choice in the local stack
;; BP field -- set of clauses in the remaining choices
;; TR field -- top of the trail
;; BG field -- top of the copy stack before allocation
;;             of the top stack. In the pair (BL, BG),
;;             BG designanes the top of the copy stack
;;             associated with the previous choice BL.

(defmacro vset (v i x) `(setf (svref ,v ,i) ,x))
(defmacro trailset(v i x) `(setf (aref ,v ,i) ,x))

(defmacro functorCopy (des largs)
  `(cons (cons (car ,des) t) ,largs))

(defmacro functorDescription (te) `(car ,te))
(defmacro functor (description) `(car ,description))

(defmacro largs (x) `(cdr ,x))
(defmacro fargs (x) `(cdr ,x))
(defmacro var? (x)
  `(and (consp ,x) (numberp (cdr ,x))))

(defmacro list? (x)
  `(eq (functor (functorDescription ,x)) '\.))

;; II. Local Stack
;;

;; The WAM environment contains [CL CP Cut E]
;;
(defmacro CL (b) `(svref Mem ,b))
(defmacro CP (b) `(svref Mem (1+ ,b)))
(defmacro Cut (b) `(svref Mem (+ ,b 2)))
(defmacro Environment (b) `(+ ,b 3))            

(defmacro push_continuation ()           
  `(progn (vset Mem *LocalPointer* CL)
	  (vset Mem (1+ *LocalPointer*) CP)))
  
(defmacro push_Environment (n)		
  `(let ((top (+ *LocalPointer* 3 ,n)))	
     (if (>= top +LocalStackOverflow+)
	 (throw 'debord (print "Local Stack Overflow")))
     (vset Mem (+ *LocalPointer* 2) Cut_pt)	
     (dotimes (i ,n top) (vset Mem (decf top) (cons 'V top)))))
 
(defmacro max_Local (nl) `(incf *LocalPointer* (+ 3 ,nl)))

(defmacro TR (b) `(svref Mem (1- ,b)))
(defmacro BP (b) `(svref Mem (- ,b 2)))
(defmacro BL (b) `(svref Mem (- ,b 3)))
(defmacro BG (b) `(svref Mem (- ,b 4)))
(defmacro BCL (b) `(svref Mem (- ,b 5)))
(defmacro BCP (b) `(svref Mem (- ,b 6)))
(defmacro AChoice (b) `(svref Mem (- ,b 7)))

(defun save_args () 
  (dotimes (i (svref xArgs 0)
	      (vset Mem (incf *LocalPointer* i) i))
    (declare (fixnum i))
    (vset Mem (+ *LocalPointer* i)
	  (svref xArgs (+ i 1)))))

(defun push_choice ()
  (save_args)
  (vset Mem (incf *LocalPointer*) CP)
  (vset Mem (incf *LocalPointer*) CL)
  (vset Mem (incf *LocalPointer*) *GPointer*)     
  (vset Mem (incf *LocalPointer*) BL)
  (vset Mem (incf *LocalPointer* 2) TR) 
  (setq BL (incf *LocalPointer*) BG *GPointer*))
        
(defun push_bpr (resto) (vset Mem (- BL 2) resto))
(defmacro size_C (b) `(+ 7 (AChoice ,b)))    

(defun pop_choice () 
  (setq *LocalPointer* (- BL (size_C BL))
	BL (BL BL)
	BG (if (zerop BL)
	       BottomG (BG BL))))

;; III. Copy Stack
;;

(defmacro push_Global (x)
  `(if (>= (incf *GPointer*) BottomL) 
       (throw 'debord (print "Heap Overflow"))
     (vset Mem *GPointer* ,x)))

(defmacro adr (v e) `(+ (cdr ,v) ,e))

(defun copy (x e)
  (cond
   ((var? x) (let ((te (ult (adr x e))))
	       (if (var? te) (genvar (cdr te)) te)))
   ((atom x) x)
   ((functorCopy (functorDescription x)
	  (mapcar (lambda(x) (copy x e)) (fargs x))) )))


(defmacro recopy (x e) `(push_Global (copy ,x ,e)))
(defmacro copy? (te)
  `(cdr (functorDescription ,te)))

;;IV. Trail
;;

(defmacro pushtrail (x te)
  (declare (ignorable te))	    
  `(cond ((>= TR +TrailOverflow+)
	  (throw 'debord (print "Trail Overflow")))
	 ( (trailset trailMem TR ,x) (incf TR) )))  

(defmacro poptrail (top) 	       
  `(do () ((= TR ,top))
     (let ((v (aref trailMem (decf TR)) ))
       (vset Mem v (cons 'V v)))))

;; mini-wam
;; utilities

(defmacro nvar (c) `(car ,c))
(defmacro head (c) `(cadr ,c))
(defmacro tail (c) `(cddr ,c))
(defmacro pred (g) `(car ,g))

(defmacro partial? (g) `(get (pred ,g) 'partial))
(defmacro user? (g) `(get (pred ,g) 'def))
(defmacro builtin? (g) `(get (pred ,g) 'evaluable))

(defmacro def_of (g) 
  `(get (pred ,g) 
      (if (largs ,g)
	       (nature (ultimate (car (largs ,g)) PCE)) 'def)))

(defmacro def_part (g) 
  `(get (pred ,g) 'partial))

(defun nature (te)
  (cond 
   ((var? te) 'def)
   ((null te) 'empty)
   ((atom te) 'atom)
   ((list? te) 'list)
   (t 'fonct)))

(defun getOutputVariables(c)
  (let* (  (fn (car c))
	  (mods (cdr (get fn 'mod)))
	  (args (cdr c)))
    (loop for x in args
	  for m in mods
	 when  (equal m '+) collect x)))

;; Begin Mauro Honorato

(defun mkCall(application)
  (let* (  (fn (car application))
	   (mods (cdr (get fn  'mod)))
	   (args (cdr application)))
    (cons fn
       (loop for x in args
	  for m in mods
	  for qx = (if (equal m '+)
		       (list 'quote x)
		       (list 'value x))
	 collect qx))))

(defun mkFunCall(application)
  (let* (  (fn (car application))
	   (mods (cdr (get fn  'mod)))
	   (args (cdr application)))
    (cons fn
       (loop for x in args
	  for m in mods
	  when (equal m '-)
	    collect (list 'value x)))))

(defun mkprologside(application)
    (let* (  (fn (car application))
	   (mods (cdr (get fn  'mod))))
      (loop for x in (cdr application)
	 for m in mods
	 collect
	   (if (equal m '+)
	       (list (gensym (symbol-name x)))
	       x))))

(defun denudeGlobalVars(s)
  (loop for x in s
     collect (if (consp x) (car x) x)))

(defun theOutputVariables(s)
  (loop for x in s when (consp x) collect (car x)))

(defun uniglobals(gs vs)
  (loop for g in gs
     for v in vs
     collect (list 'uni g v)))
;; End Mauro Honorato

(defparameter *defs* nil)

(defmacro notsafe? (x)
  `(and (not CP) (>= (cdr ,x) CL)))

(defun unifnum (x y)
    (bindte (cdr y) x))

(defun generate_specialized_unification(i arg clauses)
  (declare (ignorable clauses))
  (if  (and (consp arg)
	    (eq (car (cadr arg)) 'N))
       `(unifnum (svref xArgs ,i)
	     (ultimate ,arg env))
     `(unif (svref xArgs ,i)
	 (ultimate ,arg env))))

(defun generate_arg_unifications (nv args clauses)
  ;;(format t "nv= ~a, args= ~a~%" nv args)
  (if (eq nv 0) t 
  (list 'catch (list 'quote 'impossible)
	`(let ((env (push_Environment ,nv)))
           ,@(loop for i from 1 to nv
	           for x in args
                collect
		  (generate_specialized_unification
		   i (if (numberp x) x (list 'quote x))
		   clauses))) )))

(defun specialized_choice (unifs paq)
  (let* ((resu  (shallow_backtrack paq)  )
	 (c (car resu)) (r (cdr resu)))
    (cond ( (null r)
	    (pop_choice)
            (if (funcall unifs) ;(eq (unify_with (largs (head c))
	    ; (push_Environment (nvar c))) 'fail)
             (backtrack)                
             (when (tail c) (push_continuation)
	     (setq CP (tail c) CL *LocalPointer*)
	     (max_Local (nvar c)))))
	  ( (push_bpr r)                   
	    (when (tail c)
		  (push_continuation) 
		  (setq CP (tail c) CL *LocalPointer*)
		  (max_Local (nvar c)))))))

(defun generate_choice (unifs paq)
  `(let* ((resu  (shallow_backtrack ,paq)  )
	 (c (car resu)) (r (cdr resu)))
    (cond ( (null r)
	    (pop_choice)
            (if ,unifs ;(eq (unify_with (largs (head c))
	    ; (push_Environment (nvar c))) 'fail)
             (backtrack)                
             (when (tail c) (push_continuation)
	     (setq CP (tail c) CL *LocalPointer*)
	     (max_Local (nvar c)))))
	  ( (push_bpr r)                   
	    (when (tail c)
		  (push_continuation) 
		  (setq CP (tail c) CL *LocalPointer*)
		  (max_Local (nvar c)))))))
           
(defun provit (paq)
   (if (cdr paq)
     (let*((caput (car (cadr paq)))
           (args (largs (head caput)))
           (nv (length args))
           (unifs `(lambda()
            ,(generate_arg_unifications nv args paq))))
           (declare (ignorable caput args nv unifs))
         `(progn (push_choice)
            (let* ((resu (shallow_backtrack ,paq))
	           (c (car resu))
                   (r (cdr resu)))
              (cond ((null r)
                     (pop_choice)
                     (if (eq
                          (let ((unargs (largs (head c)))
                               (e (push_Environment (nvar c))))
                            (declare (ignorable e unargs))
                            (catch 'impossible 
                              ,@(loop for i from 1 to nv collect
                                (list 'unif 
                                  (list 'svref 'xArgs i)
                                  '(ultimate (pop unargs) e)))) )
			   'fail)
                           (backtrack)                
                           (when (tail c) 
                             (push_continuation)
                             (setq CP (tail c) 
                                   CL *LocalPointer*)
                             (max_Local (nvar c)))))
                    ((push_bpr r)                   
                     (when (tail c)
                     (push_continuation) 
                     (setq CP (tail c) CL *LocalPointer*)
                     (max_Local (nvar c))) )
                )) ))
               (let* ((c (car paq))
                      (tc (when (cdr paq)(tail paq)))
                      (args (largs (head c)))
                      (nv (length args))
                      (unifs (generate_arg_unifications 
                               nv args paq)) )
                `(if  (eq ,unifs 'fail)
                    (if (zerop BL) ;; backtrack      
                      (setq Duboulot nil)              
                      (progn (setq *LocalPointer* BL
                             *GPointer* BG Cut_pt (BL BL)
                             CP (BCP *LocalPointer*)
                             CL (BCL *LocalPointer*))
                             (load_A2)           
                             (poptrail (TR BL))
                             (pr_choice 
                               (BP *LocalPointer*))))              
                 (when ,tc (push_continuation)
                      (setq CP ,tc CL *LocalPointer*)
                      (max_Local ,nv)))  ))) 

(defun compile-args(pred ind)
  (let* ((nargs (length (cdr (cadar (get pred ind)))))
         (definition (list 'quote (get pred ind)))
         (vs (loop for i from 1 to nargs collect
              `(vset xArgs ,i
                 (let ((te (ultimate (pop largs) PCE)))
                    (cond
                      ((atom te) te)
                      ((var? te)
                       (if (notsafe? te)
                          (genvar (cdr te)) 
                          te))
                      ((copy? te) te)
                      ((recopy te PCE)))) ))))
        `(lambda()
           (let ((largs (largs PC)))
               (declare (ignorable largs))
               (vset xArgs 0 ,nargs)
               ,@vs)
               (if CP ,(provit definition)
                 (progn
                   (if (<= BL CL)
                     (setq *LocalPointer* CL))
                   (setq CP (CP CL) CL (CL CL))
                   ,(provit definition))  ))))
	    
(defun add_cl (pred c ind)
  (cond ((and (equal pred 'def))
         (let* ((nm (intern (string-downcase
                  (symbol-name (caadr  c)))))
                (args (cdr (cadr c)))
                (prologside (mkprologside (cadr c)))
                (fn (if (checkFunMode (cdr c))
                     `(lambda(,@(denudeGlobalVars prologside))
                         (uni ,(car (car prologside))
                              ,(mkFunCall (car (cdr c)))))
                      `(lambda(,@(denudeGlobalVars prologside))
                         (multiple-value-bind ,args
                            ,(mkCall  (car (cdr c)  ))
                            (declare (ignorable ,@args))
                            ,@(uniglobals
                              (theOutputVariables prologside)
                              (getOutputVariables (cadr c))))) )))
              (eval c)
              (setf (symbol-function nm) (eval fn))
              (setf (get nm 'evaluable) t)))
         ((equal pred 'mdef) (eval c)  )
         ((equal ind 'def)
          (when (not (member pred *defs*))
                (push pred *defs*))
          (setf (get pred ind) (append (get pred ind) (list c)))
          (setf (get pred 'partial) t)
          (setf (symbol-function pred)
                (eval (compile-args pred ind))))
         (t (when (not (member pred *defs*))
              (push pred *defs*))
              (setf (get pred ind) 
                 (append (get pred ind) (list c))))))

(set-macro-character
 #\$
 #'(lambda (stream char)
     (declare (ignorable char))
     (let* ( (*standard-input* stream) (c (read_code_cl)))
     
       (add_cl (if (symbolp (car c)) (car c)
		   (pred (head c ))) c 'def)
       (if (largs (head c)) 
	   (let ((b (nature (car (largs (head c))))))
	     (if (eq b 'def)
		 (mapc 
		  #' (lambda (x) (add_cl (pred (head c)) c x))
		  '(atom empty list fonct))
	       (add_cl (pred (head c)) c b)))))
     (values)))

(defun yes/no()
  (princ "More : ")
  (finish-output)
  (member (rchnsep) '(#\o #\y #\s #\d #\j #\;)))

(defun answer ()
  (printvar)
  (if (zerop BL)
      (setq Duboulot nil)
    (if (yes/no)
	(backtrack)
      (setq Duboulot nil))))
	
(defun printvar ()
  (if (null *lvar)
      (format t "Yes ~%")
    (let ((n -1))
      (mapc 
       #' (lambda (x)
	    (format t "~A = " x)
	    (write1 (ult (+ (incf n)
			    (Environment BottomL)))) (terpri))
       *lvar))))


;; mini-wam
;; unification

(defun ult (m)
  (declare (fixnum m))
  (do* ( (n m (cdr te))  (te (svref Mem n) (svref Mem n)))
       ( (not (and (var? te) (/= (cdr te) n))) te)
      (declare (fixnum n))))

(defun ultimate (x e) (if (var? x) (ult (adr x e)) x)) 
(defun val (x) (if (var? x) (ult (cdr x)) x))

(defmacro bind (x te)
  `(progn 
     (if (or (and (> ,x BottomL) (< ,x BL))
	     (<= ,x BG))
	 (pushtrail ,x ,te))
     (vset Mem ,x ,te)))

(defun bindte (xadr y)
  (declare (fixnum xadr))
  (if (or (atom y) (copy? y))
      (bind xadr y)
      (bind xadr (recopy y (Environment *LocalPointer*)))))

(defun genvar (x) (declare (fixnum x))
       (bind x (push_Global (cons 'V *GPointer*))))

(defmacro bindv (x y)
  `(if (< (cdr ,x) (cdr ,y))
       (bind (cdr ,y) ,x)
       (bind (cdr ,x) ,y))) 

(defun unify_with (largs e)           	
  (catch 'impossible 
    (do ((i 1 (1+ i)))
	((null largs))
      	(declare (fixnum i))
      (unif (svref xArgs   i)
	    (ultimate (pop largs) e)))))

(defmacro mval(x) `(if (var? ,x) (ult (cdr ,x)) ,x))

(defun unif (x y)
    (cond
     ((eql x y) t)
     ((var? y) 
	   (if (var? x)
		 (if (= (cdr x) (cdr y)) t (bindv y x))
	       (bindte (cdr y) x)))
     ((var? x)
      (bindte (cdr x) y))      
   ((or (atom x) (atom y)) (throw 'impossible 'fail))
   ((let ((b (copy? y)) (dx (pop x)) (dy (pop y)))
      (if (eq (functor dx) (functor dy))
	  (do* ( (ax x (cdr ax))
		 (vx (mval (car ax)) (mval (car ax)) )
		 (vy (pop y) (pop y)))
	       ((null ax))
	      (unif vx
		    (if b (mval vy) 
			(ultimate vy (Environment *LocalPointer*)))  ))
	(throw 'impossible 'fail))))))


;; mini-wam
;; resolution

(defun lispforward ()
  (do () ((null Duboulot))
      (cond ((null CP) (answer))
	    ( (load_PC)  
	      (cond          
	       ((user? PC) 
		(let ((d (def_of PC)))
		  (if d (pr2 d) (backtrack))))
	       ((builtin? PC)   
		(if (eq (apply (car PC) (cdr PC)) 'fail)
		    (backtrack)             
		  (cont_eval)))                
	       ((backtrack)))))))

(defun forward ()
  (do () ((null Duboulot) (format t "no More ~%"))
      (cond ((null CP) (answer))
	    ( (load_PC)
              ;; PC contains the goal
	     (cond
	       ((partial? PC)
		(funcall (car PC)))
	       ((user? PC) 
		(let ((d (def_of PC)))
		  (if d (pr2 d) (backtrack))))
	       ((builtin? PC)   
		(if (eq (apply (car PC) (cdr PC)) 'fail)
		    (backtrack)             
		  (cont_eval)))                
	       ((backtrack)))))))
         
(defun load_PC ()
  (setq PC (pop CP) PCE (Environment CL) Cut_pt BL))
				
(defmacro notsafe? (x)
  `(and (not CP) (>= (cdr ,x) CL)))

(defun cont_eval ()
  (unless CP
    (if (<= BL CL) (setq *LocalPointer* CL))
         (setq CP (CP CL) CL (CL CL))))

(defun pr_choice (paq)
  (let* ((resu  (shallow_backtrack paq)  )
	 (c (car resu)) (r (cdr resu)))
    (cond ( (null r)
	    (pop_choice)
            (if (eq (unify_with (largs (head c))
	     (push_Environment (nvar c))) 'fail)
             (backtrack)                
             (when (tail c) (push_continuation)
	     (setq CP (tail c) CL *LocalPointer*)
	     (max_Local (nvar c)))))
	  ( (push_bpr r)                   
	    (when (tail c)
		  (push_continuation) 
		  (setq CP (tail c) CL *LocalPointer*)
		  (max_Local (nvar c)))))))

(defun shallow_backtrack (paq)   
  (if (and (cdr paq) 
	   (eq (unify_with
		(largs (head (car paq)))
		(push_Environment (nvar (car paq))))
	       'fail))
      (progn
	(poptrail (TR BL))
	(setq *GPointer* BG)
	(shallow_backtrack (cdr paq)))
    paq)  )
              
(defun backtrack ()                        
  (if (zerop BL)                          
      (setq Duboulot nil)              
      (progn (setq *LocalPointer* BL *GPointer* BG Cut_pt (BL BL)
		   CP (BCP *LocalPointer*) CL (BCL *LocalPointer*))
	   (load_A2)           
	   (poptrail (TR BL))          
	   (pr_choice (BP *LocalPointer*)))))

(defun load_A2 ()
  (let ((deb (- *LocalPointer* (size_C *LocalPointer*))))
    (dotimes (i (AChoice *LocalPointer*) (vset xArgs 0 i))
      (declare (fixnum i))
		(vset xArgs (+ i 1) 
		      (svref Mem (+ deb i))))))

(defun lisploop (c)
  (setq *GPointer* BottomG *LocalPointer* BottomL TR BottomTR 
        CP nil CL 0 BL 0 BG BottomG Duboulot t Cut_pt 0)
  (push_continuation)
  (push_Environment (nvar c))
  (setq CP (cdr c) CL *LocalPointer*)
  (max_Local (nvar c))  (read-char)
  (catch 'debord (lispforward)))

(defun readProvePrintLoop (c)
  (setq *GPointer* BottomG *LocalPointer* BottomL TR BottomTR 
        CP nil CL 0 BL 0 BG BottomG Duboulot t Cut_pt 0)
  (push_continuation)
  (push_Environment (nvar c))
  (setq CP (cdr c) CL *LocalPointer*)
  (max_Local (nvar c))  (read-char)
  (catch 'debord (forward))
  (cond ( *keep-going*
	 (handler-case (readProvePrintLoop (read_prompt))
	   (error(e) (format t "Error: ~a" e) (readProvePrintLoop (read_prompt)))))
	(t (format t "Bye!~%")
	   (setf *keep-going* t))))

;; mini-wam
;; predicados predefinidos.
;;

(defvar Ob_Micro_Log 
  '(|debugvar| |one| |nt| |write| |nl| |tab| |read| |get| |get0| 
    |var| |nonvar| |atomic| |atom| |number| |clear|  |is|
    ! |fail| |true| |halt| |lisp| |div| |eqn| |gt| |ge| 
    |divi| |mod| |plus| |minus| |times| |le| |lt| 
    |name| |consult| |sult| |abolish| |cputime| |statistics|))
(mapc #'(lambda (x) (setf (get x 'evaluable) t)) Ob_Micro_Log)
  
(defmacro value (x)
  `(if (or (var? ,x) (atom ,x))
       (ultimate ,x PCE)
       (copy ,x PCE)))
(defun uni (x y) (catch 'impossible (unif (value x) y)))

(defun |debugvar|(x)
  (format t " dvar ~a " x))

;;lisp/2
(defun |lisp|(res fn)
  (uni res
       (eval (cons (intern
		    (string-upcase
		       (symbol-name
			(functor (functorDescription fn) ))))
         (mapcar (lambda(x) (value x)) (largs fn))) )) )

(defun evalfp(x)
  (cond ((numberp x) x)
	( (and (consp x) (eq (car (functor x)) '|neg|))
	 (- (evalfp (car (fargs x)))))	
	((functor x)
	 (funcall (symbol-function (car (functor x)))
		  (evalfp (car (fargs x)))
		  (evalfp (cadr (fargs x))))) ))

;;write/1 (?term)
 (defun |write| (x) (write1 (value x)))
 (defun write1 (x)
      (cond 
       ((null x) (format t "[]"))
       ((atom x) (format t "~A" x))
       ((var? x) (format t "X~A" (cdr x)))
       ((list? x) (format t "[")
	(writesl (val (cadr x)) (val (caddr x)))
	(format t "]"))
       ((writesf (functor (functorDescription x))
		 (largs x)))))

(defun writesl (tete q)
      (write1 tete)
      (cond
       ((null q))
       ((var? q) (format t "|X~A" (cdr q)))
       (t (format t ",") (writesl (val (cadr q))
				  (val (caddr q))))))

(defun writesf (fct largs)
      (format t "~A(" fct)
      (write1 (val (car largs)))
      (mapc #'(lambda (x) (format t ",")
		      (write1 (val x))) (cdr largs))
      (format t ")"))

;;nl/0
(defun |nl| () (terpri))
;;tab/1 (+int)
(defun |tab| (x)
  (dotimes (i (value x)) (format t " ")))
;;read/1 (?term)
(defun |read| (x) 
   (let ((te (read_terme)))
      (catch 'impossible 
      (unif (value x)
      (recopy (cdr te)
      (push_Environment (car te)))))))

(defun read_terme ()
   (let ((*lvar nil))
     (let ((te (read_term (rchnsep))))
       (rchnsep) (cons (length *lvar) te))))
;;get/1 (?car)
(defun |get| (x) (uni x (char-int (rchnsep))))
;;get0/1 (?car)
(defun |get0| (x) (uni x (char-int (read-char))))
;;var/1 (?term)
(defun |var| (x) (unless (var? (value x)) 'fail))
;;nonvar/1 (?term)
(defun |nonvar| (x) (if (var? (value x)) 'fail))
;;atomic/1 (?term)
(defun |atomic| (x) (if (listp (value x)) 'fail))
;;atom/1 (?term)
(defun |atom| (x) (unless (symbolp (value x)) 'fail))
;;number/1 (?term)
(defun |number| (x) (unless (numberp (value x)) 'fail))
;;fail/0
(defun |fail| () 'fail)
;;true/0
(defun |true| ())
;;divi/3 (+int,+int,?int)
(defun |divi| (z x y) (uni z (floor (value x) (value y))))
;;div/3
(defun |div| (z x y) (uni z (/ (value x) (value y))))
;;mod/3 (+int,+int,?int)
(defun |mod| (z x y) (uni z (rem (value x) (value y))))
;;plus/3 (+int,+int,?int)
(defun |plus| (z x y) (uni z (+ (value x) (value y))))
;;minus/3 (+int,+int,?int)
(defun |minus| (z x y) (uni z (- (value x) (value y))))
;;mult/3 (+int,+int,?int)
(defun |times| (z x y) (uni z (* (value x) (value y))))
;;le/2 (+int,+int)
(defun |le| (x y) (if (> (value x) (value y)) 'fail))
;;lt/2 (+int,+int)
(defun |lt| (x y) (if (>= (value x) (value y)) 'fail))
;; eqn/2
(defun |eqn| (x y) (if (not (= (value x) (value y))) 'fail))
;;gt/2
(defun |gt| (x y) (if  (<= (value x) (value y)) 'fail))
;;ge/2
(defun |ge| (x y) (if (< (value x) (value y)) 'fail))
;;name/2 (?atom,?list)
(defun undo_l (x)
  (if (atom x) x
      (cons (undo_l (val (cadr x))) (undo_l (val (caddr x))))))

(defun |name| (x y)
  (let ((b (value x)))
     (if (var? b) 
         (uni x (impl (undo_l (value y))))
         (uni y (do_l (expl b))))))

(defun impl (l) (intern (map 'string #'code-char l)))
(defun expl (at) (map 'list #'char-int (string at)))

(defun addit(c)
    (add_cl (if (symbolp (car c)) 
                (car c)
                (pred (head c ))) c 'def)
    (if (largs (head c)) 
       (let ((b (nature (car (largs (head c))))))
           (if (eq b 'def)
               (mapc 
                 #' (lambda (x) (add_cl (pred (head c)) c x))
                  '(atom empty list fonct))
                 (add_cl (pred (head c)) c b)))))
  
(defun |tolisp| (f)
  (let ((nm (value f)))
    (setf (get nm 'partial) (get nm 'def))
    (setf (get nm 'def) nil)))
     
(defun |consult| (f)
  (let* ((filename (format nil "~a" (value f)))
	 (code (rd_file filename)))
    (loop for c in code 
       do (addit c))))

;;consult/1 (+atom)
(defun |sult| (f) (format t "~A~%"
			(load (format nil "~A" (value f))  )))

;; abolish/1
(defun |abolish| (p)
  (mapc  #'(lambda (x) (setf (get p x) nil))
	 '(atom empty list fonct def)))

;; clear/0
(defun |clear| ()
  (mapc #'(lambda(x) (|abolish| x)) *defs*))

;; cputime/1
(defun |cputime| (x)
  (uni x (float (/ (get-internal-run-time)
		   internal-time-units-per-second))))

;; statistics/0 
(defun |statistics| ()
  (format t " local stack : ~A (~A used)~%"
	  (- +LocalStackOverflow+ BottomL) 
          (- *LocalPointer* BottomL))
  (format t " global stack : ~A (~A used)~%"
	  BottomL (- *GPointer* BottomG))
  (format t " trail : ~A (~A used)~%"
	  (- (array-dimension trailMem 0) BottomTR)
	  (- TR BottomTR)))

(defun |halt| ()
  (setf *keep-going* nil))

(defvar *G* (the fixnum 0))
(defvar *L* (the fixnum 0))
(defvar *TR* (the fixnum 0))
(defvar *BG* (the fixnum 0))

(defun |one| ()
  (setq *G* *GPointer* *L* *LocalPointer* *TR* TR *BG* BG))

(defun |is|(x fx)
  (uni x (evalfp  (value fx ))))

(defun |nt|(n)
    (setq BL (Cut CL) BG (if (zerop BL) BottomG (BG BL))
	  *LocalPointer* (+ CL 3 n))
    (when *TR* 
       (setq TR *TR* *GPointer* *G* *G* nil *TR* nil)) )

;;cut/0
(defun ! (n)
  (setq TR (if (zerop BL) BottomTR (TR BL))
	 BL (Cut CL)
	BG (if (zerop BL) BottomG (BG BL))	      
	       *LocalPointer* (+ CL 3 n)) )

(defun bye()
  (cl-user::exit))
