#lang eopl

; Exercise 1.17
(define (down lst)
  (map (lambda (e) (list e)) lst))


; Exercise 1.26
(define (up lst)
  (apply append
         (map (lambda (x)
                (if (list? x)
                    x
                    (list x)))
              lst)))
; Exercise 1.27
(define (flatten slist)
  (cond
    [(null? slist) '()]
    [(symbol? slist) (list slist)]
    [else
     (apply append (map flatten slist))]))

; Exercise 1.28
(define (merge loi1 loi2)
  (cond
    [(null? loi1) loi2]
    [(null? loi2) loi1]
    [(< (car loi1) (car loi2))
     (cons (car loi1) (merge (cdr loi1) loi2))]
    [else
     (cons (car loi2) (merge loi1 (cdr loi2)))]))

; Exercise 1.29
(define (sort loi)
  (define (split loi)
    (cond [(null? loi) (cons '() '())]
          [(null? (cdr loi)) (cons loi '())]
          [else
           (let ((p (split (cddr loi))))
             (cons (cons (car loi) (car p))
                   (cons (cadr loi) (cdr p))))]))
  
  (cond [(null? loi) '()]
        [(null? (cdr loi)) loi]
        [else
         (let ((p (split loi)))
           (merge (sort (car p)) (sort (cdr p))))]))

; Exercise 1.30
(define (sort/predicate pred loi)
  (define (merge loi1 loi2)
    (cond
      [(null? loi1) loi2]
      [(null? loi2) loi1]
      [(pred (car loi1) (car loi2))
       (cons (car loi1) (merge (cdr loi1) loi2))]
      [else
       (cons (car loi2) (merge loi1 (cdr loi2)))]))
  
  (define (split loi)
    (cond [(null? loi) (cons '() '())]
          [(null? (cdr loi)) (cons loi '())]
          [else
           (let ((p (split (cddr loi))))
             (cons (cons (car loi) (car p))
                   (cons (cadr loi) (cdr p))))]))
  
  (cond [(null? loi) '()]
        [(null? (cdr loi)) loi]
        [else
         (let ((p (split loi)))
           (merge (sort/predicate pred (car p)) (sort/predicate pred (cdr p))))]))

; Exercise 1.31
(define (leaf content) content)
(define (interior-node content l r) (list content l r))
(define (leaf? bintree) (not (list? bintree)))
(define (lson bintree) (cadr bintree))
(define (rson bintree) (caddr bintree))

(define (contents-of bintree)
  (if (leaf? bintree)
      bintree
      (car bintree)))

; Exercise 1.33
(define (mark-leaves-with-red-depth bintree)
  (define (helper bintree number)
    (if (leaf? bintree)
        (leaf number)
        (if (eqv? 'red (contents-of bintree))
            (interior-node (contents-of bintree)
                           (helper (lson bintree) (+ number 1))
                           (helper (rson bintree) (+ number 1)))
            (interior-node (contents-of bintree)
                           (helper (lson bintree) number)
                           (helper (rson bintree) number)))))
  (helper bintree 0))

; Exercise 1.34
(define (path n bst)
  (cond [(< n (car bst)) (cons 'left (path n (cadr bst)))]
        [(> n (car bst)) (cons 'right (path n (caddr bst)))]
        [else '()]))

; Exercise 1.35
(define (number-leaves bintree)
  (define (helper bintree next-number)
    (if (leaf? bintree)
        (cons (leaf next-number) (+ next-number 1))
        (let* ((left-result (helper (lson bintree) next-number))
               (left-tree   (car left-result))
               (mid-number  (cdr left-result))
               (right-result (helper (rson bintree) mid-number))
               (right-tree   (car right-result))
               (final-number (cdr right-result)))
          (cons (interior-node (contents-of bintree)
                               left-tree
                               right-tree)
                final-number))))
  (car (helper bintree 0)))

