#lang scheme

;;; SICP
;;; Section 1: Building Abstractions with Procedures

;;; 1.1 The Elements of Programming

;; 1.1.6 Conditional Expressions and Predicates

;; Exercise 1.1
;; trivial

;; Exercise 1.2
(/ (+ 5 4 (- 2 (- 3 (+ 6 (/ 4 5))))) (* 3 (- 6 2) (- 2 7)))

;; Exercise 1.3
(define (square x) (* x x))

(define (sum-of-2-squares x y z)
  (if (> x y)
      (if (> y z)
          (+ (square x) (square y))
          (+ (square x) (square z)))
      (if (> x z)
          (+ (square x) (square y))
          (+ (square y) (square z)))))

;; Exercise 1.4

;; In the following expression we may say, that the `if` special form may
;; return functions, instead of values. Here if b <= 0, then it is
;; subtracted from a, thus it is equivalent to a + |b|.
(define (a-plus-abs-b a b)
  ((if (> b 0) + -) a b))

;; Exercise 1.5

;; Here the execution of the function `p` makes it execute itself
;; infinitely. If we use normal-order evaluation, the `p` is never
;; called, as x == 0 and `p` is in the else branch of the `if` special
;; form.
;;
;; In applicative-order evaluation however, the arguments are
;; evaluated first, thus the `test` function is never executed, and
;; the interpreter enters infinite recursion.
(define (p) (p))
(define (test x y)
  (if (= x 0) 0 y))
(test 0 (p))

;; 1.1.7 Example: Square Roots by Newton’s Method

;; first variant, as in SICP
(define (sqrt-iter guess x)
  (if (good-guess? guess x)
      guess
      (sqrt-iter (improve-guess guess x) x)))

(define (improve-guess guess x)
  (average guess (/ x guess)))

(define (average x y)
  (/ (+ x y) 2))

(define (good-guess? guess x)
  (< (abs (- (square guess) x)) 0.001))

;; we took name 'sqroot' because 'sqrt' is used by system
(define (sqroot x) 
  (sqrt-iter 1.0 x))

;; Exercise 1.6

;; `if` is a special form. It is not an ordinary function. We remember
;; that Scheme uses applicative-order evaluation, thus when functions
;; are executed, their arguments are evaluated first. This causes an
;; infinite recursion in `sqrt-iter2`. Special forms however don't
;; evaluate their arguments.
(define (new-if predicate then-clause else-clause)
  (cond (predicate then-clause)
        (else else-clause)))

(define (sqrt-iter2 guess x)
  (new-if (good-guess? guess x)
          guess
          (sqrt-iter2 (improve-guess guess x)
                     x)))

;; Exercise 1.7

;;     > (sqroot 10)
;;     3.162277665175675
;;     > (sqroot 0.1)
;;     0.316245562280389
;;     > (sqroot 0.01)
;;     0.10032578510960605
;;     > (sqroot 0.001)
;;     0.04124542607499115
;;     > (sqroot 0.0001)
;;     0.03230844833048122

;; As seen from above, starting from 0.001, `sqroot` solutions for
;; small numbers become inadequate.

(define (sqrt-iter3 oldguess guess x)
  (if (good-guess-2? oldguess guess x)
      guess
      (sqrt-iter3 guess (improve-guess guess x) x)))

;; Here we substitute `(- (square guess) x)` with `(/ (- guess
;; oldguess) oldguess)` and track change from the oldguess to guess.
;; When difference between oldguess to guess is below some tolerance
;; (here 0.001), we are satisfied with the result.
(define (good-guess-2? oldguess guess x)
  (< (abs (/ (- guess oldguess) oldguess)) 0.001))

(define (sqroot2 x)
  (sqrt-iter3 0.5 1.0 x))

;; Exercise 1.8
(define (cube x) (* x x x))

(define (cbrt-iter guess x)
  (if (cbrt-good-guess? guess x)
      guess
      (cbrt-iter (cbrt-improve-guess guess x) x)))

(define (cbrt-good-guess? guess x)
  (< (abs (- (cube guess) x)) 0.001))

(define (cbrt-improve-guess guess x)
  (/ (+ (/ x (square guess)) (* 2 guess)) 3))

;; 1.2.1 Linear Recursion and Iteration

(define (factorial n)
  (if (= n 1)
      1
      (* n (factorial (- n 1)))))

(define (factorial2 n)
  (fact-iter 1 1 n))

(define (fact-iter product counter max-count)
  (if (> counter max-count)
      product
      (fact-iter (* counter product)
                 (+ counter 1)
                 max-count)))

;; Exercise 1.9

;; Example:
;; (+ 3 4)
;; (inc (+ 2 4))
;; (inc (inc (+ 1 4)))
;; (inc (inc (inc 4)))
;; (inc (inc 5))
;; (inc 6)
;; 7
;; Recursive process
(define (+ a b)
  (if (= a 0) b (inc (+ (dec a) b))))

;; Example:
;; (+ 3 4)
;; (+ 2 5)
;; (+ 1 6)
;; (+ 0 7)
;; 7
;; Iterative process
(define (+ a b)
  (if (= a 0) b (+ (dec a) (inc b))))

;; Exercise 1.10

;; f(n) = A(0, n) computes 0
;; g(n) = A(1, n) computes 2^n
;; h(n) = A(2, n) computes 2↑↑n

(define (akerman x y)
  (cond ((= y 0) 0)
        ((= x 0) (* 2 y))
        ((= y 1) 2)
        (else (akerman (- x 1)
                 (akerman x (- y 1))))))

;; 1.2.2 Tree Recursion

;; Fibonacci
(define (fibonacci n)
  (fibonacxi-iter 1 0 n))

(define (fibonacci-iter a b count)
  (if (= count 0)
      b
      (fibonacxi-iter (+ a b) a (- count 1))))

;; Money change
(define (count-change amount)
  (cc amount 5))

(define (cc amount kinds-of-coins)
  (cond ((= amount 0) 1)
        ((or (< amount 0) (= kinds-of-coins 0)) 0)
        (else (+ (cc amount
                     (- kinds-of-coins 1))
                 (cc (- amount
                         (first-denomination kinds-of-coins))
                     kinds-of-coins)))))

(define (first-denomination kinds-of-coins)
  (cond ((= kinds-of-coins 1) 1)
        ((= kinds-of-coins 2) 5)
        ((= kinds-of-coins 3) 10)
        ((= kinds-of-coins 4) 25)
        ((= kinds-of-coins 5) 50)))

;; Exercise 1.11

;; This function adds 3 previous elements instead of 2 in fibonacci
(define (fib3 n)
  (if (< n 3)
      n
      (+ (fib3 (- n 1))
         (fib3 (- n 2))
         (fib3 (- n 3)))))

(define (fib3-new n)
  (if (< n 3)
      n
      (fib3-iter 2 1 0 n)))

(define (fib3-iter a b c count)
  (if (= count 0)
      c
      (fib3-iter (+ a b c) a b (- count 1))))

;; For english variant:
(define (fib3-orig n)
  (if (< n 3)
      n
      (+ (fib3-orig (- n 1))
         (* 2 (fib3-orig (- n 2)))
         (* 3 (fib3-orig (- n 3))))))

(define (fib3-new-orig n)
  (if (< n 3)
      n
      (fib3-iter-orig 2 1 0 n)))

(define (fib3-iter-orig a b c count)
  (if (= count 0)
      c
      (fib3-iter-orig (+ a (* 2 b) (* 3 c)) a b (- count 1))))

;; Exercise 1.12
(define (pascal-triangle row col)
  (if (or (= col 1) (= row col))
      1
      (+ (pascal-triangle (- row 1) col)
         (pascal-triangle (- row 1) (- col 1))))) ;; !

(define (pascal-triangle-new row col)
  (if (or (= col 1) (= row col))
      1
      (pascal-triangle-iter 1 1 row col)))

(define (pascal-triangle-iter a b rowcount colcount)
  (if (and  (= rowcount 0) (= colcount 0))
      b
      (pascal-triangle-iter (+ a b) a rowcount colcount)))

;; Exercise 1.13
;; Basis step: Fib(1) = 1, Fib(2) = 1.
;; φ = (1 + sqrt(5)) / 2, ψ = (1 - sqrt(5)) / 2
;; Inductive step: F_{i+1} = F_i + F_{i-1}
;; (φ^{n+1} + ψ^{n+1}) / sqrt(5) = (φⁿ + ψⁿ) / sqrt(5) + (φ^{n-1} + ψ^{n-1}) / sqrt(5)
;; (φⁿ + ψⁿ) / sqrt(5) + (φ^{n-1} + ψ^{n-1}) / sqrt(5) =
;; = (φ*(φ^{n-1} + φ^{n-1}) - ψ*(ψ^{n-1} + ψ{n-1})) / sqrt(5) =
;; = (φ * φⁿ - ψ * ψⁿ) / sqrt(5) =
;; = (φ^{n+1} - ψ^{n+1}) / sqrt(5) ∎

;; 1.2.3 Orders of Growth

;; Exercise 1.14

;; Requires drawing a tree

;; Exercise 1.15

(define (cube x) (* x x x))

(define (p x) (- (* 3 x) (* 4 (cube x))))

(define (sine angle)
  (if (not (> (abs angle) 0.1))
      angle
      (p (sine (/ angle 3.0)))))

;; Rewrite the `p` function above as:

;;    (define (p x)
;;      (print ".")
;;      (newline)
;;      (- (* 3 x) (* 4 (cube x))))

;; Execute (sine 12.15). `p` is called 5 times, because 5 dots are
;; printed.

;; * TODO: explain The order of growth

;; 1.2.4 Exponentiation

(define (fast-expt b n)
  (cond ((= n 0) 1)
        ((even?-2 n) (square (fast-expt b (/ n 2))))
        (else (* b (fast-expt b (- n 1))))))

(define (even?-2 n)
  (= (remainder n 2) 0))

;; Exercise 1.16
(define (fast-expt-iter a b n)
  (if (= n 0)
      a
      (if (even? n)
          (fast-expt-iter a (square b) (/ n 2))
          (fast-expt-iter (* a b) b (- n 1)))))

;; Exercise 1.17
(define (double a)
  (* a 2))

(define (halve a)
  (/ a 2))

(define (fast-* a b)
  (cond ((= b 0) 0)
        ((= b 1) a)
        ((even? b) (double (fast-* a (halve b))))
        (else (+ a (fast-* a (- b 1))))))

;; Exercise 1.18
(define (fast-*-iter a b c)
  (cond ((= b 0) c)
        ((even? b) (fast-*-iter (double a) (halve b) c))
        (else (fast-*-iter a (- b 1) (+ c a)))))

;; Exercise 1.19
;; transformations
(define (fib-t n)
  (fib-t-iter 1 0 0 1 n))

(define (fib-t-iter a b p q count)
  (cond ((= count 0) b)
        ((even? count)
         (fib-t-iter a
                   b
                   (+ (square p) (square q)) ; вычислить p’
                   (+ (* 2 p q) (square q)) ; вычислить q’
                   (/ count 2)))
        (else (fib-t-iter (+ (* b q) (* a q) (* a p))
                        (+ (* b p) (* a q))
                        p
                        q
                        (- count 1)))))

;; 1.2.5 Greatest Common Divisors
(define (gcd1 a b)
  (if (= b 0)
      a
      (gcd1 b (remainder a b))))

;; Exercise 1.20:
;; * TODO finish

;; 1.2.6 Example: Testing for Primality
(define (smallest-divisor n)
  (find-divisor n 2))

(define (find-divisor n test-divisor)
  (cond ((> (square test-divisor) n) n)
        ((divides? test-divisor n) test-divisor)
        (else (find-divisor n (+ test-divisor 1)))))

(define (divides? a b)
  (= (remainder b a) 0))

(define (prime? n)
  (= n (smallest-divisor n)))

(define (expmod base exp m)
  (cond ((= exp 0) 1)
        ((even? exp)
         (remainder (square (expmod base (/ exp 2) m))
                    m))
        (else
         (remainder (* base (expmod base (- exp 1) m))
                    m))))

(define (fermat-test n)
  (define (try-it a)
    (= (expmod a n n) a))
  (try-it (+ 1 (random (- n 1)))))

(define (fast-prime? n times)
  (cond ((= times 0) true)
        ((fermat-test n) (fast-prime? n (- times 1)))
        (else false)))

;; Exercise 1.21
;; trivial

;; Exercise 1.22
(define runtime
  current-milliseconds)

(define (timed-prime-test n)
  (start-prime-test n (runtime)))

(define (start-prime-test n start-time)
  (if (prime? n)
      (report-prime n (- (runtime) start-time))
      #f))

(define (report-prime n elapsed-time)
  (display n)
  (display " *** ")
  (display elapsed-time)
  (newline)
  true)

(define (odd? n)
  (= (remainder n 2) 1))

(define (search-for-primes number-from prime-count)
  (if (> prime-count 0)
      (if (and (timed-prime-test number-from) (odd? number-from))
          (search-for-primes (+ number-from 1) (- prime-count 1))
          (search-for-primes (+ number-from 1) prime-count))
      null))

;; > (search-for-primes (expt 10 10) 3)
;; 10000000019 *** 7
;; 10000000033 *** 7
;; 10000000061 *** 7
;; > (search-for-primes (expt 10 11) 3)
;; 100000000003 *** 20
;; 100000000019 *** 15
;; 100000000057 *** 15
;; > (search-for-primes (expt 10 12) 3)
;; 1000000000039 *** 49
;; 1000000000061 *** 45
;; 1000000000063 *** 45
;; > (search-for-primes (expt 10 13) 3)
;; 10000000000037 *** 154
;; 10000000000051 *** 140
;; 10000000000099 *** 139
;; 154 / 49 ≈ 49 / 20 ≈ 20 / 7 ≈ sqrt(10), Θ(sqrt(n))

;; Exercise 1.23
(define (smallest-divisor-adv n)
  (find-divisor-adv n 2))

(define (next-divisor test-divisor)
  (if (= test-divisor 2)
      3
      (+ test-divisor 2)))

(define (find-divisor-adv n test-divisor)
  (cond ((> (square test-divisor) n) n)
          ((divides? test-divisor n) test-divisor)
          (else (find-divisor n (next-divisor test-divisor)))))

(define (timed-prime-test-adv n)
  (define (prime?-adv)
    (= n (smallest-divisor-adv n)))  
  (define (start-prime-test-adv start-time)
    (if (prime?-adv)
        (report-prime n (- (runtime) start-time))
        false))
  (start-prime-test-adv (runtime)))

;; * TODO answer to this:
;; Since this modification halves the number of
;; test steps, you should expect it to run about twice as fast. Is this
;; expectation confirmed? If not, what is the observed ratio of the
;; speeds of the two algorithms, and how do you explain the fact that
;; it is different from 2?

;; Exercise 1.24

(define (timed-prime-test-fast n)
  (define (start-prime-test-fast start-time)
    (if (fast-prime? n 10000)
        (report-prime n (- (runtime) start-time))
        false))
  (start-prime-test-fast (runtime)))

;; Here instead of giving huge numbers we increase the number to
;; repeat Fermat's procedure, because (random) accepts only numbers <
;; 2^{31}. (fast-prime? n 10000) is enough to see the growth.

;; > (begin
;;    (timed-prime-test-fast 1009)
;;    (timed-prime-test-fast 1013)
;;    (timed-prime-test-fast 1019)
;;    (timed-prime-test-fast 10007)
;;    (timed-prime-test-fast 10009)
;;    (timed-prime-test-fast 10037)
;;    (timed-prime-test-fast 100003)
;;    (timed-prime-test-fast 100019)
;;    (timed-prime-test-fast 100043)
;;    (timed-prime-test-fast 1000003)
;;    (timed-prime-test-fast 1000033)
;;    (timed-prime-test-fast 1000037))
;; 1009 *** 27
;; 1013 *** 18
;; 1019 *** 18
;; 10007 *** 24
;; 10009 *** 23
;; 10037 *** 23
;; 100003 *** 29
;; 100019 *** 28
;; 100043 *** 29
;; 1000003 *** 33
;; 1000033 *** 33
;; 1000037 *** 33
;;
;; We see that time increases by constant value, when input increases
;; by the power of 10. This confirms that Fermat's test has Θ(log n)
;; order of growth. Time for 10⁶ is roughly 2 times the time for 10³.

;; Exercise 1.25

;; * TODO solve

;; Exercise 1.26

;; * TODO solve

;; Exercise 1.27

(define (carmichael-test n)
  (define (i a n)
    (cond ((>= a n) true)
          ((not (= (expmod a n n) a)) false) ;; what's shorter for (not (= ...)) ?
          (else (i (add1 a) n))))
  (i 1 n))

;; > (carmichael-test 1008)
;; #f
;; > (carmichael-test 1009)
;; #t
;; > (carmichael-test 561)
;; #t
;; > (carmichael-test 1105)
;; #t
;; > (carmichael-test 1729)
;; #t
;; > (carmichael-test 2465)
;; #t
;; > (carmichael-test 2821)
;; #t
;; > (carmichael-test 6601)
;; #t
;;
;; true for primes and carmichael numbers, false for any other

;; Exercise 1.28

;; * TODO solve (very important)

;; 1.3 Formulating Abstractions with Higher-Order Procedures

(define (sum term a next b)
  (if (> a b)
      0
      (+ (term a)
         (sum term (next a) next b))))

(define (identity x) x)

;; Exercise 1.29

(define (simpson f a b n)
  (define h (/ (- b a) n))
  (define (iter k sum)
    (if (= k n)
        sum
        (let ((y (cond ((or (= k 0) (= k n)) (y k))
                       ((even? k) (* 2 (y k)))
                       (else (* 4 (y k))))))
          (iter (+ k 1) (+ sum y)))))
  (define (y k)
    (f (+ a (* k h))))
  (/ (* h (iter 0 0)) 3.0))

;; Exercise 1.30

(define (sum-iter term a next b)
  (define (iter a result)
    (if (> a b)
        result
        (iter (next a) (+ (term a) result))))
  (iter a 0))

;; Exercise 1.31

;; a.
(define (product term a next b)
  (if (> a b)
      1
      (* (term a)
         (product term (next a) next b))))

(define (factorial n)
  (product identity 1 add1 n))

(define (pi-approximation)
  (define approximation 100)
  (define (next-2 n)
    (+ 2 n))
  ;; 2 * 4 / 3 * 3 or 4 * 6 / 5 * 5 etc
  (define (pi-term n)
    (/ (* (- n 1) (+ n 1)) (square n)))
  (* 4 (product pi-term 3.0 next-2 approximation)))

;; b.
(define (product-iter term a next b)
  (define (i a result)
    (if (> a b)
        result
        (i (next a) (* (term a) result))))
  (i a 1))

;; Exercise 1.32

;; a.
(define (accumulate combiner null-value term a next b)
  (if (> a b)
      null-value
      (combiner (term a)
                (accumulate term (next a) next b))))

(define (sum-acc term a next b)
  (accumulate + 0 term a next b))

(define (product-acc term a next b)
  (accumulate * 1 term a next b))

;; b.
(define (accumulate-iter combiner null-value term a next b)
  (define (i a result)
    (if (> a b)
        result
        (i (next a) (combiner (term a) result))))
  (i a null-value))

;; Exercise 1.33

(define (filtered-accumulate filter combiner null-value term a next b)
  (define (i a result)
    (cond ((> a b) result)
          ((filter a) (i (next a) (combiner (term a) result)))
          (else (i (next a) result))))
  (i a null-value))

;; a.
(define (sum-of-squares-of-primes a b)
  (filtered-accumulate prime? + 0 square a add1 b))

;; b.
(define (product-of-integers-relatively-prime n)
  (define (relatively-prime? a b)
    (= (gcd a b) 1))
  (filtered-accumulate relatively-prime? * 1 identity 1 add1 n))

;; 1.3.2 Constructing procedures using lambda

;; Exercise 1.34

(define (f g)
  (g 2))

;; (f f) expands to (f 2), which expands to (2 2). There can't be no
;; procedure called 2, so the interpreter stops with the following
;; error:
;; 
;; procedure application: expected procedure, given: 2; arguments
;; were: 2

;; 1.3.3 Procedures as general methods

;; Exercise 1.35



;; Exercise 1.45 ???
;;special: generalized root
(define (genrt-iter guess x n)
  (if (genrt-good-guess? guess x n)
      guess
      (genrt-iter (genrt-improve-guess guess x n) x n)))

(define (genrt-good-guess? guess x n)
  (< (abs (- (fast-expt guess n) x)) 0.001))

(define (genrt-improve-guess guess x n)
  (/ (+ (/ x (fast-expt guess (- n 1))) (* (- n 1) guess)) n))
