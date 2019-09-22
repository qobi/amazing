#!r6rs

(define-record-type dual-number (fields epsilon primal tangent))

(define *eta-expansion?* #f)

(define *tag-substitution?* #t)

(define *section9?* #f)

;;; One of equation-24d, equation-38, or equation-41
(define *function-substitution* 'equation-24d)

(define *epsilon* 0)

(define (generate-epsilon)
 (set! *epsilon* (+ *epsilon* 1))
 *epsilon*)

(define (subst epsilon1 epsilon2 x)
 (cond ((real? x) x)			;Equation (24a)
       ((dual-number? x)
	(if (= (dual-number-epsilon x) epsilon2)
	    ;; Equation (24b)
	    (make-dual-number
	     epsilon1 (dual-number-primal x) (dual-number-tangent x))
	    ;; Equation (24c)
	    (make-dual-number
	     (dual-number-epsilon x)
	     (subst epsilon1 epsilon2 (dual-number-primal x))
	     (subst epsilon1 epsilon2 (dual-number-tangent x)))))
       ((procedure? x)
	(lambda (y)
	 (case *function-substitution*
	  ((equation-24d)
	   ;; Equation (24d)
	   (let ((epsilon3 (generate-epsilon)))
	    (subst epsilon2 epsilon3
		   (subst epsilon1 epsilon2 (x (subst epsilon3 epsilon2 y))))))
	  ((equation-38)
	   ;; Equation (38)
	   (subst epsilon2 epsilon1 (x (subst epsilon1 epsilon2 y))))
	  ;; Equation (41)
	  ((equation-41) (x y))
	  (else (error "A")))))
       (else (error "B"))))

(define (prim epsilon x)
 (cond ((real? x) x)
       ((dual-number? x)
	(if (= (dual-number-epsilon x) epsilon)
	    (dual-number-primal x)
	    (make-dual-number (dual-number-epsilon x)
			      (prim epsilon (dual-number-primal x))
			      (prim epsilon (dual-number-tangent x)))))
       ((procedure? x)
	(if *tag-substitution?*
	    (lambda (y)
	     (let ((epsilon2 (generate-epsilon)))
	      (subst epsilon
		     epsilon2
		     (prim epsilon (x (subst epsilon2 epsilon y))))))
	    (lambda (y) (prim epsilon (x y)))))
       (else (error "C"))))

(define (tg epsilon x)
 (cond ((real? x) 0)			;Equation (8a)
       ((dual-number? x)
	(if (= (dual-number-epsilon x) epsilon)
	    ;; Equation (8b)
	    (dual-number-tangent x)
	    ;; Equation (8c)
	    (make-dual-number (dual-number-epsilon x)
			      (tg epsilon (dual-number-primal x))
			      (tg epsilon (dual-number-tangent x)))))
       ((procedure? x)
	(if *tag-substitution?*
	    ;; Equation (23)
	    (lambda (y)
	     (let ((epsilon2 (generate-epsilon)))
	      (subst epsilon
		     epsilon2
		     (tg epsilon (x (subst epsilon2 epsilon y))))))
	    ;; Equation (8e)
	    (lambda (y) (tg epsilon (x y)))))
       (else (error "D"))))

(define (bun epsilon x x-prime)
 (cond ((and (or (real? x) (dual-number? x))
	     (or (real? x-prime) (dual-number? x-prime)))
	;; Equation (30a)
	(make-dual-number epsilon x x-prime))
       ((and (procedure? x) (procedure? x-prime))
	(if *tag-substitution?*
	    ;; Equation (31)
	    (lambda (y)
	     (let ((epsilon2 (generate-epsilon)))
	      (subst epsilon epsilon2
		     (bun epsilon
			  (x (subst epsilon2 epsilon y))
			  (x-prime (subst epsilon2 epsilon y))))))
	    ;; Equation (30b)
	    (lambda (y) (bun epsilon (x y) (x-prime y)))))
       (else (error "E"))))

(define (lift-real->real f df/dx)
 (letrec ((self (lambda (x)
		 (if (dual-number? x)
		     (let ((epsilon (dual-number-epsilon x)))
		      (bun epsilon
			   (self (prim epsilon x))
			   (d* (df/dx (prim epsilon x)) (tg epsilon x))))
		     (f x)))))
  self))

(define (lift-real*real->real f df/dx1 df/dx2)
 (letrec ((self (lambda (x1 x2)
		 (if (or (dual-number? x1) (dual-number? x2))
		     (let ((epsilon (if (dual-number? x1)
					(dual-number-epsilon x1)
					(dual-number-epsilon x2))))
		      (bun epsilon
			   (self (prim epsilon x1) (prim epsilon x2))
			   (d+ (d* (df/dx1 (prim epsilon x1) (prim epsilon x2))
				   (tg epsilon x1))
			       (d* (df/dx2 (prim epsilon x1) (prim epsilon x2))
				   (tg epsilon x2)))))
		     (f x1 x2)))))
  self))

;;; Equation (5a)
(define d+ (lift-real*real->real + (lambda (x1 x2) 1) (lambda (x1 x2) 1)))

;;; Equation (5b)
(define d* (lift-real*real->real * (lambda (x1 x2) x2) (lambda (x1 x2) x1)))

(define dexp (lift-real->real exp (lambda (x) (dexp x))))

(define (j* f)
 (lambda (x x-prime)
  (if *eta-expansion?*
      (if (procedure? (f x))
	  ;; Equation (32a)
	  (lambda (y) ((j* (lambda (x) ((f x) y))) x x-prime))
	  ;; Equation (32b)
	  (let ((epsilon (generate-epsilon)))
	   (tg epsilon (f (bun epsilon x x-prime)))))
      ;; Equation (33)
      (let ((epsilon (generate-epsilon)))
       (tg epsilon (f (bun epsilon x x-prime)))))))

(define (d f)
 (lambda (x)
  (cond (*section9?* ((j* f) x 1))	;Equation (34)
	(*eta-expansion?*
	 (if (procedure? (f x))
	     ;; Equation (18a)
	     (lambda (y) ((d (lambda (x) ((f x) y))) x))
	     ;; Equation (18b)
	     (let ((epsilon (generate-epsilon)))
	      (tg epsilon (f (make-dual-number epsilon x 1))))))
	;; Equation (8d)
	(else (let ((epsilon (generate-epsilon)))
	       (tg epsilon (f (make-dual-number epsilon x 1))))))))

;;; Equation (9)
;;; R->((R->R)->(R->R))
(define (s u) (lambda (f) (lambda (x) (f (d+ x u)))))

;;; Equation (11)
(define d-hat ((d s) 0))

;;; Siskind & Pearlmutter (IFL 2005) Equation (2)
(write ((d (lambda (x) (d* x ((d (lambda (y) (d+ x y))) 1)))) 1))
(newline)
;;; Siskind & Pearlmutter (HOSC 2008) pages 363-364
(write ((d (lambda (x) (d* x ((d (lambda (y) (d* x y))) 2)))) 1))
(newline)
;;; Equation (13 left) with h=exp and y=1
(write ((d-hat (d-hat dexp)) 1))
(newline)
;;; Equation (13 right) with h=exp and y=1
(write ((d (d dexp)) 1))
(newline)

;;; Equation (20a)
(define (pair a) (lambda (d) (lambda (m) ((m a) d))))

;;; Equation (20b)
(define (fst c) (c (lambda (a) (lambda (d) a))))

;;; Equation (20c)
(define (snd c) (c (lambda (a) (lambda (d) d))))

;;; Equation (20d)
(define (t u) ((pair (dexp (d* u u))) (lambda (f) (lambda (x) (f (d+ x u))))))

(write ((d (lambda (x) (dexp (d* x x)))) 1))
(newline)
;;; Equation (20e)
(write (fst ((d t) 1)))
(newline)
(let* ((p ((d t) 0))			;Equation (20f)
       ;; Equation (20h)
       (d-vec (snd p)))
 ;; Equation (20g)
 (write (fst p))
 (newline)
 ;; Equation (20i)
 (write ((d-vec (d-vec dexp)) 1))
 (newline))

(define pi (* 2 (acos 0)))

(define (f x) x)

;;; Equation (21)
(define (g x) (let ((t (f x))) (lambda (p) (p t))))

;;; Equation (22)
(define (h x)
 (let ((c (g x)))
  (d+ (c (lambda (t) t)) ((c (lambda (t) (lambda (u) (d* t u)))) pi))))

;;; Example from page 12
(write ((d h) 8))
(newline)

;;; Equation (35a)
(define (map-pair f) (lambda (l) ((pair (f (fst l))) (f (snd l)))))

;;; Equation (35b)
(define (sqr x) (d* x x))

;;; Equation (35c)
(let ((result (((j* map-pair) sqr (d sqr)) ((pair 5) 10))))
 (write (fst result))
 (newline)
 (write (snd result))
 (newline))

;;; Equation (39)
(define (v u) (lambda (f1) (lambda (f2) (lambda (x) ((f1 f2) (d+ x u))))))

;;; Equation (40)
(define (i x) x)

;;; Example from page 20
(write (((((d v) 0) (((d v) 0) i)) dexp) 1))
(newline)

;;; Equation (42a)
;;; R->(box R)
(define (box x) (lambda (m) (m x)))

;;; Equation (42b)
;;; (box R)->R
(define (unbox x) (x (lambda (x) x)))

;;; Equation (42c)
;;; (R->R)->((box R)->(box R))
(define (wrap f) (lambda (x) (box (f (unbox x)))))

;;; Equation (42d)
;;; ((box R)->(box R))->(R->R)
(define (unwrap f) (lambda (x) (unbox (f (box x)))))

;;; Equation (42e)
;;; ((R->R)->(R->R))->(((box R)->(box R))->((box R)->(box R)))
(define (wrap2 f) (lambda (g) (lambda (x) (box ((f (unwrap g)) (unbox x))))))

;;; Equation (42f)
;;; (R->((R->R)->(R->R)))->(R->(((box R)->(box R))->((box R)->(box R))))
(define (wrap2-result f) (lambda (x) (wrap2 (f x))))

;;; Equation (42g)
(define wrapped-d-hat ((d (wrap2-result s)) 0))

;;; Equation (42i) with h-exp and y=1
(write
 ((unwrap (((d (wrap2-result s)) 0) (((d (wrap2-result s)) 0) (wrap dexp)))) 1))
(newline)

;;; Equation (42j) with h-exp and y=1,
;;;          when *function-substitution*='equation-24d
;;;       or (42k) with h-exp and y=1,
;;;          when *function-substitution*='equation-41
(write ((unwrap (wrapped-d-hat (wrapped-d-hat (wrap dexp)))) 1))
(newline)
(exit)
