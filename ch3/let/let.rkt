#lang eopl

(require "parse.rkt")

(define (foldl proc init lst)
  (if (null? lst)
      init
      (foldl proc (proc (car lst) init) (cdr lst))))

(define (foldr proc init lst)
  (foldl proc init (reverse lst)))

(define (andmap proc lst)
  (if (null? lst)
      #t
      (let ((val (proc (car lst))))
        (if val (andmap proc (cdr lst)) val))))

(define (ormap proc lst)
  (if (null? lst)
      #f
      (let ((val (proc (car lst))))
        (if val val (ormap proc (cdr lst))))))

(define pair-of
  (lambda (car-pred? cdr-pred?)
    (lambda (p)
      (and (car-pred? (car p))
           (cdr-pred? (cdr p))))))

(define list-of
  (lambda (pred)
    (lambda (val)
      (or (null? val)
          (and (pair? val)
               (pred (car val))
               ((list-of pred) (cdr val)))))))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define report-expval-extractor-error
  (lambda (type val)
    (eopl:error 'expval-extractor-error "~s not a ~s" val type)))

; Env = Var → SchemeVal
; empty-env : () → Env
(define empty-env
  (lambda ()
    (lambda (search-var)
      (report-no-binding-found search-var))))

; extend-env : Var × SchemeVal × Env → Env
(define extend-env
  (lambda (saved-var saved-val saved-env)
    (lambda (search-var)
      (if (eqv? search-var saved-var)
          saved-val
          (apply-env saved-env search-var)))))

; apply-env : Env × Var → SchemeVal
(define apply-env
  (lambda (env search-var)
    (env search-var)))

(define identifier? symbol?)

(define-datatype program program?
  (a-program
   (exp1 expression?)))

(define-datatype expression expression?
  (const-exp
   (num number?))
  (add-exp
   (exp1 expression?)
   (exp2 expression?))
  (diff-exp
   (exp1 expression?)
   (exp2 expression?))
  (mul-exp
   (exp1 expression?)
   (exp2 expression?))
  (int-div-exp
   (exp1 expression?)
   (exp2 expression?))
  (zero?-exp
   (exp1 expression?))
  (if-exp
   (exp1 expression?)
   (exp2 expression?)
   (exp3 expression?))
  (var-exp
   (var identifier?))
  (let-exp
   (var identifier?)
   (exp1 expression?)
   (body expression?))
  (minus-exp
   (exp1 expression?))
  (equal?-exp
   (exp1 expression?)
   (exp2 expression?))
  (greater?-exp
   (exp1 expression?)
   (exp2 expression?))
  (less?-exp
   (exp1 expression?)
   (exp2 expression?))
  (cons-exp
   (exp1 expression?)
   (exp2 expression?))
  (car-exp
   (exp1 expression?))
  (cdr-exp
   (exp1 expression?))
  (null?-exp
   (exp1 expression?))
  (emptylist-exp)
  (list-exp
   (exps (list-of expression?)))
  (cond-exp
   (clauses (list-of (pair-of expression? expression?)))))

; init-env : () → Env
; usage: (init-env) = [i=⌈1⌉,v=⌈5⌉,x=⌈10⌉]
(define init-env
  (lambda ()
    (extend-env
     'i (num-val 1)
     (extend-env
      'v (num-val 5)
      (extend-env
       'x (num-val 10)
       (empty-env))))))

(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (pair-val
   (val1 expval?)
   (val2 expval?))
  (emptylist-val))

; expval->num : ExpVal → Int
(define expval->num
  (lambda (val)
    (cases expval val
      (num-val (num) num)
      (else (report-expval-extractor-error 'num val)))))

; expval->bool : ExpVal → Bool
(define expval->bool
  (lambda (val)
    (cases expval val
      (bool-val (bool) bool)
      (else (report-expval-extractor-error 'bool val)))))

; expval->bool : ExpVal → Pair
(define expval->pair
  (lambda (val)
    (cases expval val
      (pair-val (val1 val2) (cons val1 val2))
      (else (report-expval-extractor-error 'pair val)))))

; run : String → ExpVal
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

; value-of-program : Program → ExpVal
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (value-of exp1 (init-env))))))

; value-of : Exp × Env → ExpVal
(define value-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (var-exp (var) (apply-env env var))
      (add-exp (exp1 exp2)
               (let ((val1 (value-of exp1 env))
                     (val2 (value-of exp2 env)))
                 (let ((num1 (expval->num val1))
                       (num2 (expval->num val2)))
                   (num-val
                    (+ num1 num2)))))
      (diff-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val2)))
                    (num-val
                     (- num1 num2)))))
      (mul-exp (exp1 exp2)
               (let ((val1 (value-of exp1 env))
                     (val2 (value-of exp2 env)))
                 (let ((num1 (expval->num val1))
                       (num2 (expval->num val2)))
                   (num-val
                    (* num1 num2)))))
      (int-div-exp (exp1 exp2)
                   (let ((val1 (value-of exp1 env))
                         (val2 (value-of exp2 env)))
                     (let ((num1 (expval->num val1))
                           (num2 (expval->num val2)))
                       (num-val
                        (quotient num1 num2)))))
      (zero?-exp (exp1)
                 (let ((val1 (value-of exp1 env)))
                   (let ((num1 (expval->num val1)))
                     (if (zero? num1)
                         (bool-val #t)
                         (bool-val #f)))))
      (equal?-exp (exp1 exp2)
                  (let ((val1 (value-of exp1 env))
                        (val2 (value-of exp2 env)))
                    (let ((num1 (expval->num val1))
                          (num2 (expval->num val2)))
                      (if (eqv? num1 num2)
                          (bool-val #t)
                          (bool-val #f)))))
      (greater?-exp (exp1 exp2)
                    (let ((val1 (value-of exp1 env))
                          (val2 (value-of exp2 env)))
                      (let ((num1 (expval->num val1))
                            (num2 (expval->num val2)))
                        (if (> num1 num2)
                            (bool-val #t)
                            (bool-val #f)))))
      (less?-exp (exp1 exp2)
                 (let ((val1 (value-of exp1 env))
                       (val2 (value-of exp2 env)))
                   (let ((num1 (expval->num val1))
                         (num2 (expval->num val2)))
                     (if (< num1 num2)
                         (bool-val #t)
                         (bool-val #f)))))
      (if-exp (exp1 exp2 exp3)
              (let ((val1 (value-of exp1 env)))
                (if (expval->bool val1)
                    (value-of exp2 env)
                    (value-of exp3 env))))
      (let-exp (var exp1 body)
               (let ((val1 (value-of exp1 env)))
                 (value-of body
                           (extend-env var val1 env))))
      (minus-exp (exp1)
                 (let ((val1 (value-of exp1 env)))
                   (let ((num1 (expval->num val1)))
                     (num-val (- num1)))))
      (cons-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (pair-val val1 val2)))
      (car-exp (exp1)
               (let ((val1 (value-of exp1 env)))
                 (car (expval->pair val1))))
      (cdr-exp (exp1)
               (let ((val1 (value-of exp1 env)))
                 (cdr (expval->pair val1))))
      (null?-exp (exp1)
                 (let ((val1 (value-of exp1 env)))
                   (cases expval val1
                     (emptylist-val () (bool-val #t))
                     (else (bool-val #f)))))
      (emptylist-exp ()
                     (emptylist-val))
      (list-exp (exps)
                (foldr (lambda (exp exps)
                         (pair-val (value-of exp) exps))
                       (emptylist-val) exps))
      (cond-exp (clauses)
                (let ((exp (ormap (lambda (clause)
                                    (if (expval->bool (value-of (car clause) env))
                                        (cdr clause)
                                        #f))
                                  clauses)))
                  (if exp
                      (value-of exp env)
                      (eopl:error 'cond "none of the tests succeeds.")))))))

