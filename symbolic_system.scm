;Group Member
;Hernan Lozano, Tenzin Chhosphel, Edward Chung
;
;Symbolic Algebra System
;- Basic data type : An equation represented with the syntax tree. Ex. f(x) = 2*x + x^2 ==> (list (list 2 * x) + (list x ^ 2))
;
;Premitive data types
;    1. expression = e ::= constant || variable || (e 'op e) || ()
;       - An expression can be a number or a variable. 
;    2. op ::= '+ || '* || '- || '^ || '/
;       - op is binary operator between two expressions.
;
;Constructors
;    1. (make-sum e1 e2) ::= (list e1 '+ e2)
;    2. (make-product e1 e2) ::= (list e1 '* e2)
;    3. (make-sub e1 e2) ::= (list e1 '- e2)
;    4. (make-exp e1 e2) ::= (list e1 '^ e2)
;    5. (make-div e1 e2) ::= (list e1 '/ e2)
;    6. (make-equ e1 e2) ::= (list e1 '= e2)
;    
;Selectors
;    1. (select-first e) ::= (car e)
;    2. (select-second e) ::= (caddr e) 
;    3. (select-op e) ::= (cadr e)
;   
;
;    
;Operations
;    1. (sum? e) ::= (eq? (select-op e) '+)
;    2. (product? e) ::= (eq? (select-op e) '*)
;    3. (sub? e) ::= (eq? (select-op e) '-)
;    4. (exp? e) ::= (eq? (select-op e) '^)
;    5. (div? e) ::= (eq? (select-op e) '/)
;    6. (equation? e) ::= (eq? (select-op e) '=)
;    7. (variable? e) ::= (symbol? e)
;    8. (num? e) ::= (number? e)
;    9. (print-e e) ::= (display '((select-first e) (select-op e) (select-second)))
; -----------------------------------------------------------------
;  *10. (deriv expression var)  ::= derivative of e with respect to var  
;  *11. (expand e)::= equivalent expression in expanded view
;  *12. (simplify e) ::= equivalent expression with like terms combined
;  *13. (solve e var) ::= given an equation and var, attempt to isolate var.
;  *14. (evaluate e var num) ::= evaluates given expression e, using var and number 
;  
; -----------------------------------------------------------------
;*** guys I starred the above points because I am not sure if we want those points written here
;    or down below the expressions primitives... then we can argue that 9,10,12,12,etc are
;    extensions to the language and then just prove each separate.
; -----------------------------------------------------------------
;
; -----------------------------------------------------------------
;	ABSTRACTION LAYER 
; -----------------------------------------------------------------
;  At this point all the data that is included in our
;  infix representation of algebraic representations taken 
;  as parts of the language. Using now the above as primitives,
;  we can do an expension of the language to include:


; -----------------------------------------------------------------
;	DERIVATIVE - EXTENSION OF THE LANGUAGE
; -----------------------------------------------------------------
; carryout the functions for solving derivatives of any expressions
; implemented with the above constructors. Dtermine the rules for 
; differentiating an expression with respect to a variable var.
;
;	10. (deriv expression var) => expression
;
; -----------------------------------------------------------------
;	SIMPLIFY - EXTENSION OF THE LANGUAGE
; -----------------------------------------------------------------
;
;	12. (simplify expression) => expression
;
; -----------------------------------------------------------------
;	EVALUATE - EXTENSION OF THE LANGUAGE
; -----------------------------------------------------------------
;
;	14. (eval-exp expression) => expression (or number)
;
; -----------------------------------------------------------------
;	SOLVE - EXTENSION OF THE LANGUAGE (possible extension)
; -----------------------------------------------------------------
;   13. (solve expression) => expression
;       - In order to accomplish this, we may have to extend our basic data primitives so that it can respresent equality between two expressions.
;         --> Ex. If we let e1 = ( ( 2 * x ) + (y + 2 ) )
;                           e2 = 0
;                 then, we may have e3 = ( e1 = e2 ) = ( ( 2 * x ) + (y + 2 ) = 0 ). Then, we might come up with some function in terms of other. 
;                 f(x) = ( ( -y - 2 ) / 2 ) or f(y) = ( -2 * ( 1 + x ) )
;
; -----------------------------------------------------------------
;	CRITICAL POINT - EXTENSION OF THE LANGUAGE (possible extension)
; -----------------------------------------------------------------
;   ??. The previous extension may allow us to find critical point of the function at certain point in the domain. Our (deriv expression var) can deal with
;       a function with multivariable. This means that if the input expression is multivariable function, then our (deriv expression var) can be extended to
;       output a vector that contains the partial derivatives respect to each variable (gradient). If we assume that our (solve expression) works properly, 
;       then we will be able to come up with candidate points that might be critical points in the function domain. By recursively calling our (deriv expression var)
;       to find sencond derivative (Hessian), then we can determine if the candidate point is a saddle point, maximum or minimum. One possible function definition 
;       would be
;                     (critical expression candidate) ==> max || min || saddle || no conclusion
;
; -----------------------------------------------------------------
;  DEBUGGING FUNCTIONS
; -----------------------------------------------------------------
(define (debug1  a) (display a)(newline))
(define (debug2  a b) (display a)(display " ---- ")(display b)(newline))
(define (debug3  a b c) (display a)(display " ---- ")(display b)(display " ---- ")(display c)(newline))


; -----------------------------------------------------------------



; ====================================================================================================
; Constructors
; All the constructors make an equation using binary operator. Therefore, implementing
; those constructors are straight forward since we just need to make a list with two
; expressions on both sides of the operator.
; Always make symbol on left side for readability.
(define (make-sum e1 e2)
  (cond ((and (number? e1) (number? e2)) (+ e1 e2))
        ((number? e1) (if (= e1 0) e2
                          (list e2 '+ e1)))
        ((number? e2) (if (= e2 0) e1
                          (list e1 '+ e2)))
        (else ; If e1 == e2, then 2*e1 or 2*e2
         (if (eq? e1 e2) (make-product e1 e2)
             (list e1 '+ e2)))))

(define (make-product e1 e2)
  (cond ((and (number? e1) (number? e2)) (* e1 e2))
        ((number? e1)
         (if (= e1 0) 0
             (list e2 '* e1)))
        ((number? e2)
         (if (= e2 0) 0
             (list e1 '* e2)))
        (else
         (if (eq? e1 e2) (make-exp e1 2)
             (list e1 '* e2)))))

(define (make-sub e1 e2)
  (cond ((and (number? e1) (number? e2)) (- e1 e2))
        ((number? e1) 
         (if (= e1 0) (make-product e2 -1)
             (make-sum e1 (make-product e2 -1))))
        ((number? e2)
         (if (= e2 0) e1
             (make-sum e1 (* -1 e2))))
        (else
         (make-sum e1 e2))))


(define (make-exp e1 e2)
  (cond ((and (number? e1) (number? e2))
         (expt e1 e2))
        (else
         (cond ((and (exp? e1) (exp? e2))
                (if (eq? (select-first e1) (select-first e2)) 
                    (list (select-first e1) '^ (+ (select-second e1) (select-second e2)))
                    (list e1 '^ e2)))
               (else 
                (list e1 '^ e2))))))


(define (make-div e1 e2)
  (cond ((and (number? e1) (number? e2))
         (if (= e2 0) ; Undefined
             (error "Denominator cannot be zero!")
             (/ e1 e2)))
        ((number? e1)
         (list e1 '/ e2))
        ((number? e2) ; We need to check if e2 is zero here too.
         (cond ((= e2 0) (error "Denominator cannot be zero!"))
               ((= e2 1) e1)
               (else
                (list e1 '/ e2))))
        (else
         (list e1 '/ e2))))

(define (make-equ e1 e2)
  (cond((or (equation? e1)
            (equation? e2)) (error "equations only work for: expression = expression"))
       (else (list e1 '= e2))))
             

(define (select-first e)
  (car e))

(define (select-second e)
  (caddr e))

(define (select-op e)
  (cadr e))
; ====================================================================================================

; ====================================================================================================
; Operations
(define (sum? e)
  (cond ((or (variable? e) (num? e)) #f)
        (else
         (eq? (select-op e) '+))))

(define (product? e)
  (cond ((or (variable? e) (num? e)) #f)
        (else
         (eq? (select-op e) '*))))
(define (sub? e)
  (cond ((or (variable? e) (num? e)) #f)
        (else
         (eq? (select-op e) '-))))
(define (exp? e)
  (cond ((or (variable? e) (num? e)) #f)
        (else
         (eq? (select-op e) '^))))
(define (div? e)
  (cond ((or (variable? e) (num? e)) #f)
        (else
         (eq? (select-op e) '/))))
(define (equation? e)
  (cond((or (variable? e) (num? e)) #f)
       (else
        (eq? (select-op e) '=))))


(define (variable? e)
  (symbol? e))

(define (num? e)
  (number? e))

(define (same-variable? e1 e2)
  (eq? e1 e2))


(define (print-e e)
  (cond((equation? e) (display (select-first e)) (display (select-op e)) (display (select-second e))(newline))
       ((or (num? e) (variable? e)) (display e)(newline))
       (else (display (select-first e)) (display (select-op e)) (display (select-second e))(newline))))
; ====================================================================================================

;; testing
(define sum0 (make-sum 'x 1))
(define sum1 (make-sum 'x 2))
(define sum2 (make-sum 3 'x))
(define subt1 (make-sub 'x 2))
(define subt2 (make-sub 3 'x))
(define prod1 (make-product sum1 'x))
(define exp1 (make-exp prod1 3))
(define div1 (make-div exp1 3))
(define equ1 (make-equ sum1 sum2))

;;Testing for exp expression with same base.
(define e1 (make-exp 'x 2))
(define e2 (make-exp 'x 2))
(define e3 (make-exp e1 e2))

;; testing
;(sum? sum1)
;(sum? prod1)
;(product? prod1)
;(product? sum1)
;(exp? exp1)
;(exp? prod1)
;(div? div1)
;(div? sum1)

; ====================================================================================================
; Evaluate
; Pre : It takes three arguments an e, list of variables, and values associated with each variables.
;       We assume that number of variables and values are same.
; Post : There are cases.
;        Case 1. If e contains less of equal number of variables in the list, return number.
;        Case 2. If e contains more variables than in the list, return a proper expression 
;                such that all variables in the expression is replaced with associated values.
; To prove this function works correctly, that is if we input an expression with list of variables and list of values,
; then it returns what we wanted, we need several assumptions.
; Assumption 1 : (nth-element index variables) returns the value in values with proper index (0 base).
;                 ex. If values = '(1 2 3) and index = 1, then (nth-element index values) = 2.
; Assumption 2 : (return-index var lst) returns the proper index of var in lst.
;                ex. If var = 'x and lst = '(y u x), then (return-index var lst) = 2.
; Assumption 3 : All the constructors and selectors do its job properly.

; Proof.
; The function evaluate takes three arguments, e as an expression, variables as a list of variables, and
; values as a list of values associated with the list of variables. There are cases we need to consider.
; Case 1 : variables and values might be empty. If this is the case, then there are no associated "variables"
;          in e that we want to replace with numbers in values, then we just return the same expression as e.
;          This works ok because whatever the e is (sum? or product? or ...), eventually each part of e
;          will reach to the basic expression such as number or variable by recusive calls of evaluate. If 
;          it finds num? then return number = e. If it find variable? then nth-element tries to extract the
;          associated value. But since "variables" is empty, (variable-found? e variables) will return #f.
;          Then, the function just return e and make proper expression. 
;
; Case 2 : When variables and values are not empty, then it try to replace all variables in "variables" with
;          associated values in "values". So if the input e is number?, then it outputs e. If e is a variable,
;          then it tries to find e in "variables". If it finds any, then replace with the associated value else
;          it outputs e. If e is some complex expression, then the function evaluate will be recursivlely called
;          and eventually rechese to variable. Then, same process is repeated as above.
; 
; This proof is based on the assumption that the function evaluate and other neccessary function work properly
; on some sub-expression.

(define (evaluate e variables values)
  (cond ((num? e) e)
        ((variable? e)
         (if (variable-found? e variables) (nth-element (return-index e variables) values)
             e))
        ((sum? e) (make-sum (evaluate (select-first e) variables values)
                            (evaluate (select-second e) variables values)))
        ((product? e) (make-product (evaluate (select-first e) variables values)
                                    (evaluate (select-second e) variables values)))
        ((sub? e) (make-sub (evaluate (select-first e) variables values)
                            (evaluate (select-second e) variables values)))
        ((div? e) (make-div (evaluate (select-first e) variables values)
                            (evaluate (select-second e) variables values)))
        (else 'error)))

; test cases.
(define test (make-sum sum2 'y))
(define test-mult (make-product sum2 'y))
(define test-sub (make-sub sum2 'y))
(define test-div (make-div sum2 'y))

; varialbe-found
; pre : It takes var which we are looking for, and a a list of variables.
; post : Return boolean. If var is in variables, return true otherwise return false.
(define variable-found?
  (lambda (var variables)
    (cond ((null? variables) #f)
          ((eq? (car variables) var) #t)
          (else 
           (variable-found? var (cdr variables))))))


; return-index
; pre : It takes a variable var and a list variables.
; post : If var is in variables, return the index otherwise return -1 indicating that cannot find var.
(define return-index
  (lambda (var variables)
    (define (helping count ele lst)
      (cond ((null? lst) -1)
            ((eq? (car lst) ele) count)
            (else (helping (+ count 1) ele (cdr lst)))))
    (helping 0 var variables)))


; nth-element
; The assumtion is that lst has enough element. 
; pre : It takes an index and a lst where index is 0 based and lst has enough element.
; post : It returns nth element in the list.
(define nth-element
  (lambda (index lst)
    (cond ((or (= index 0) (< index 0)) (car lst))
          (else
           (nth-element (- index 1) (cdr lst))))))

; ====================================================================================================

; integral, inputs : e, list of variables and intervals
(define integral
  (lambda (e . intervals)
    (define length (/ 1 10)) ; Equal length in each interval.
    (define (iterate-int e fixed-range iter-range) ; fixed-range = start, iter-range = '(start end)
      (cond ((> (+ (car iter-range) length) (cadr iter-range)) '())
            (else
             (cons (* (evaluate e (extract-var intervals) (list fixed-range (car iter-range)))
                      (+ fixed-range length) ; base1
                      (+ (car iter-range) length)) ; base2
                      (iterate-int e fixed-range (list (+ (car iter-range) length) (car (cdr iter-range))))))))
    (define (iterate-fixed e partition-range iter-range)
      (cond ((null? partition-range) '())
            (else
             (append (iterate-int e (car partition-range) iter-range) ; first find integral with fixed range.
                     (iterate-fixed e (cdr partition-range) iter-range)))))
    ;(iterate-fixed e '(1 2 3) '(1 5))))
    (let ((partition-range (partition length (cadr (car intervals))))) ; take x range and partition.
      (let ((volumes (iterate-fixed e partition-range (cadr (cadr intervals)))))
        (add-all volumes)))))

(define add-all
  (lambda (lst)
    (cond ((null? lst) 0)
          (else
           (+ (car lst) (add-all (cdr lst)))))))
(define extract-var
  (lambda (lst)
    (map car lst)))

(define partition
  (lambda (length range)
    (cond ((> (+ (car range) length) (cadr range)) '())
          (else
           (cons (+ (car range) length) (partition length (list (+ (car range) length) (cadr range))))))))
; Documentation
(define (deriv expression var)
  (cond((number? expression) 0)
       ((variable? expression) (if (same-variable? expression var) 1 0))
       ((sum? expression) (make-sum (deriv (select-first expression) var) 
                                    (deriv (select-second expression) var)))
       ((sub? expression) (make-sub (deriv (select-first expression) var)
                                    (deriv (select-second expression) var)))
       ((product? expression) (make-sum (make-product (deriv (select-first expression) var)
                                                      (select-second expression))
                                        (make-product (select-first expression)
                                                      (deriv (select-second expression) var))))
       ((exp? expression) (if (number? (select-second expression))
                              (make-product (make-product (select-second expression)
                                            (make-exp (select-first expression)
                                                      (make-sub (select-second expression) 1)))
                                            (deriv (select-first expression) var))
                                (error "no exponential functions implemented")))
  
       ((div? expression) (deriv (make-product (select-first expression)
                                               (make-exp (select-second expression) -1))
                                 var))
       (else (error "infix operator not yet implemented"))))


(define (expand-e e)
  ;(debug1 e)
  ;(debug2 "sum? " (sum? e))
 (cond((equation? e) (make-equation (expand-e (select-first e))
                                    (expand-e (select-first e))))
      ;EXPANDING A SUM EXPRESSION
      ((sum? e) (define e1 (select-first e))
                (define e2 (select-second e))
                (cond((or (num? e1) (variable? e1)) ;(debug3 e e1 e2)
                                                    (make-sum e1
                                                              (expand-e e2)))
                     ((sum? e1)  (define e1a (select-first e1))
                                 (define e1b (select-second e1))
                                 (make-sum (expand-e e1a)
                                           (make-sum (expand-e e1b)
                                                     (expand-e e2))))
                     ((sub? e1) (define e1a (select-first e1))
                                (define e1b (select-second e1))
                                (make-sum (expand-e e1a)
                                          (make-sum (make-sub 0 (expand-e e1b)) 
                                                    (expand-e e2))))
                     ((product? e1)(define e1a (select-first e1))
                                   (define e1b (select-second e1)) 
                                   (make-sum (make-product (expand-e e1a)
                                                           (expand-e e1b))
                                             (expand-e e2)))
                     ((div? e1)(define e1a (select-first e1))
                               (define e1b (select-second e1)) 
                               (make-sum (make-div (expand-e e1a)
                                                   (expand-e e1b))
                                         (expand-e e2)))
                     (else (make-sum (expand-e e1)
                                     (expand-e e2)))))
      ;EXPANDING A SUBTRACTION EXPRESSION
      ((sub? e) (define e1 (select-first e))
                (define e2 (select-second e))
                (cond((or (num? e1) (variable? e1)) ;(debug3 e e1 e2)
                                                    (make-sum e1
                                                              (make-sub 0
                                                                        (expand-e e2))))
                     ((sum? e1)  (define e1a (select-first e1))
                                 (define e1b (select-second e1))
                                 (make-sum (expand-e e1a)
                                           (make-sum (expand-e e1b)
                                                     (expand-e e2))))
                     ((sub? e1) (define e1a (select-first e1))
                                (define e1b (select-second e1))
                                (make-sum (expand-e e1a)
                                          (make-sum (make-sub 0 (expand-e e1b)) 
                                                    (make-sub 0 (expand-e e2)))))
                     ((product? e1)(define e1a (select-first e1))
                                   (define e1b (select-second e1)) 
                                   (make-sum (make-product (expand-e e1a)
                                                           (expand-e e1b))
                                             (make-sub 0 (expand-e e2))))
                     ((div? e1)(define e1a (select-first e1))
                               (define e1b (select-second e1)) 
                               (make-sum (make-div (expand-e e1a)
                                                   (expand-e e1b))
                                         (make-sub 0 (expand-e e2))))
                     (else (make-sum (expand-e e1)
                                     (make-sub 0 (expand-e e2))))))
      ;EXPANDING A MULTIPLICATION EXPRESSION      
      ((product? e) (define e1 (select-first e))
                    (define e2 (select-second e))
                    (cond((sum? e1) (define e1a (select-first e1))
                                    (define e1b (select-second e1))
                                    (make-sum (make-product (expand-e e1a)
                                                            (expand-e e2))
                                              (make-product (expand-e e1b)
                                                            (expand-e e2))))
                         ((sub? e1) (define e1a (select-first e1))
                                    (define e1b (select-second e1))
                                    (make-sum (make-product (expand-e e1a)
                                                            (expand-e e2))
                                              (make-sub 0 
                                                        (make-product (expand-e e1b)
                                                                      (expand-e e2)))))
                         ((sum? e2) (define e2a (select-first e2))
                                    (define e2b (select-second e2))
                                    (make-sum (make-product (expand-e e1)
                                                            (expand-e e2a))
                                              (make-product (expand-e e1)
                                                            (expand-e e2b))))
                         ((sub? e2) (define e2a (select-first e2))
                                    (define e2b (select-second e2))
                                    (make-sum (make-product (expand-e e1)
                                                            (expand-e e2a))
                                              (make-sub 0 
                                                        (make-product (expand-e e1)
                                                                      (expand-e e2b)))))



                         (else (make-product (expand-e e1)
                                             (expand-e e2)))))
      ;EXPANDING A DIVISION EXPRESSION
      ((div? e) (define e1 (select-first e))
                (define e2 (select-second e))
                (cond((sum? e1) (define e1a (select-first e1))
                                (define e1b (select-second e1))
                                (make-sum (make-div (expand-e e1a)
                                                    (expand-e e2))
                                          (make-div (expand-e e1b)
                                                    (expand-e e2))))
                     ((sub? e1) (define e1a (select-first e1))
                                (define e1b (select-second e1))
                                (make-sum (make-div (expand-e e1a)
                                                    (expand-e e2))
                                          (make-sub 0 
                                                    (make-div (expand-e e1b)
                                                              (expand-e e2)))))
                     (else (make-div (expand-e e1)
                                     (expand-e e2)))))
      (else e)))


(define (expand-e-all exp)
 (define new-exp (expand-e exp))
  ;(debug1 exp)
 (cond((equal? exp new-exp) exp)
      (else (expand-e-all new-exp))))


;LIKE TERMS
;for now, we will only be programming the nterface for single variable expressions of the form 3 * x or x * 3
(define (like-terms? e1 e2)
  (cond((number? e1) (number? e2))
       ((and (var? e1) (var? e2)) (same-variable? e1 e2))))
       
        

;
;;(simplify exp) only works for sum for now
;;It only works for single variable expression
;;to test, do expansion first,
;;e.g., (simplify (expand-e-all exp))
;(define (simplify exp)
;  (define (new-simplify new-exp simplified-exp var-coeff const)
;    (cond ((num? new-exp) (make-sum simplified-exp (+ new-exp const)))
;          ((variable? new-exp) (make-sum (make-sum simplified-exp new-exp) const)) 
;          ((sum? new-exp)
;           ; If (sum? new-exp) is true, then either (select-first new-exp) is number or variable.
;           (cond ((number? (select-first new-exp)) 
;                  (new-simplify (select-second new-exp) 
;                                simplified-exp 
;                                var-coeff 
;                                (+ (select-first new-exp) const)))
;              
;                 ((num? simplified-exp)
;                  (new-simplify (select-second new-exp) 
;                                (make-sum (select-first new-exp) simplified-exp)
;                                var-coeff
;                                const))
;                 
;                 ((variable? simplified-exp)
;                  (if (same-variable? (select-first new-exp) simplified-exp)
;                      (new-simplify (select-second new-exp) 
;                                    (make-product (+ var-coeff 1) (select-first new-exp))
;                                    (+ var-coeff 1)
;                                    const)
;                      ; else variables are not same
;                      ; this is the case for multi-variable expression
;                      (new-simplify (select-second new-exp) 
;                                    (make-sum (select-first new-exp) simplified-exp)
;                                    var-coeff
;                                    const)))
;                 
;                 ((same-variable? (select-first new-exp) (select-first simplified-exp))
;                  (new-simplify (select-second new-exp) 
;                                (make-product (select-first new-exp) (+ var-coeff 1))
;                                (+ var-coeff 1)
;                                const))
;           
;                 (else (new-simplify (select-second new-exp) 
;                                     (make-sum (select-first new-exp) simplified-exp)
;                                     (+ var-coeff 1)
;                                     const))))
;          
;          (else (display "need to implement other operators"))))
;  
;  (new-simplify exp 0 1 0))
;                  
;                                       
;
;;testing simplification for sum
;;(define testsum (make-sum 3 (make-sum 'x 3)))
;;(define testsum2 (make-sum 'x (make-sum 'x 3)))
;; (simplify testsum2)
;; (simplify (expanded-e-all answer4))
;
;       
;;testing expand-e
(define sum3 (make-sum sum1 sum0))
(define sum4 (make-sum sum3 sum2))
(define sum5 (make-sum sum4 sum1))

(define subt3 (make-sub subt1 subt2))
(define subt4 (make-sub subt3 subt1))
(define subt5 (make-sub subt4 subt2))

(define mye (make-sub sum5 subt5))

(print-e mye)
(define myexpand (expand-e-all mye))
(print-e myexpand)

;(define equation1 (make-equ sum1 sum2))
;(print-e equation1)
;sum5
;
;(define answer1 (expand-e-all sum5))
;answer1
;(print-e sum5)

;(print-e sum4)
;(print answer1)
;(expand-e '(((x + 1) + 2) + (x + 3)))
;
;;simplify testing
;
;(print-e sum5)
;(print-e answer1)
;(print-e (simplify answer1))

