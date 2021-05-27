// Copyright (C) 2021  Dmitry Zolotarev <dvzolotarev@gmail.com>

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
module Basics

(** * Basics: Functional Programming in Coq *)

(* REMINDER:

          #####################################################
          ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
          #####################################################

   (See the [Preface] for why.)
*)

(** * Introduction *)

(** * Data and Functions *)

(** ** Enumerated Types *)

(** ** Days of the Week *)

type day =
  | Monday
  | Tuesday
  | Wednesday
  | Thursday
  | Friday
  | Saturday
  | Sunday

val next_weekday: d: day -> Tot day
let next_weekday = function
    | Monday -> Tuesday
    | Tuesday -> Wednesday
    | Thursday -> Friday
    | _ -> Monday

let next_weekday_test () : Lemma (next_weekday Friday == Monday) =
  normalize_term_spec (next_weekday Friday)

let next_weekday_test' () : Lemma
  (next_weekday (next_weekday Saturday) == Tuesday) =
    normalize_term_spec (next_weekday (next_weekday Saturday))

(** ** Booleans *)

type my_bool =
  | T
  | F

val negb: b: my_bool -> Tot my_bool
let negb = function
  | T -> F
  | F -> T

val andb: b1: my_bool -> b2: my_bool -> Tot my_bool
let andb b1 b2 =
  match b1 with
  | T -> b2
  | F -> F

val orb: b1: my_bool -> b2: my_bool -> Tot my_bool
let orb b1 b2 =
  match b1 with
  | T -> T
  | F -> b2

let test_orb1 () : Lemma (orb T T == T) =
  normalize_term_spec (orb T T)

let test_orb2 () : Lemma (orb F F == F) =
  normalize_term_spec (orb F F)

let test_orb3 () : Lemma (orb F T == T) =
  normalize_term_spec (orb F T)

let test_orb4 () : Lemma (orb T T == T) =
  normalize_term_spec (orb T T)

(** **** Exercise: 1 star, standard (nandb)

    Provide a definition of the function nandb.
    Use the following lemmas (test_nandb1 ... test_nandb4)
    to know about it's behavior.
    Also fix the lemmas by replacing admit() with commented code
    and make sure that they are proved *)

assume val nandb: a: my_bool -> b: my_bool -> my_bool

let test_nandb1 () : Lemma (nandb T F == T) =
  admit() // normalize_term_spec (nandb T F)

let test_nandb2 () : Lemma (nandb F F == T) =
  admit() // normalize_term_spec (nandb T F)

let test_nandb3 () : Lemma (nandb F T == T) =
  admit() // normalize_term_spec (nandb F T)

let test_nandb4 () : Lemma (nandb T T == F) =
  admit() // normalize_term_spec (nandb T T)

(** [] *)

(** **** Exercise: 1 star, standard (andb3)

    Do the same for the andb3 function below.
    This function should return T when all of its inputs are T,
    and F otherwise. *)

assume val andb3: a: my_bool -> b: my_bool -> c: my_bool -> my_bool

let test_andb31 () : Lemma (andb3 T T T == T) =
  admit() // normalize_term_spec (andb3 T T T)

let test_andb32 () : Lemma (andb3 F T T == F) =
  admit() // normalize_term_spec (andb3 F T T)

let test_andb33 () : Lemma (andb3 T F T == F)  =
  admit() // normalize_term_spec (andb3 F T T)

let test_andb34 () : Lemma (andb3 T T F == F) =
  admit() // normalize_term_spec (andb3 F T T)

(** [] *)

(** ** Types *)

type rgb =
  | Red
  | Green
  | Blue

type color =
  | Black
  | White
  | Primary: p: rgb -> color

val isred: c: color -> Tot my_bool
let isred = function
  | Black -> F
  | White -> F
  | Primary Red -> T
  | Primary _ -> F

(** ** Tuples *)

type bit =
  | B0
  | B1

type nybble =
  | Bits: b0: bit -> b1: bit -> b2: bit -> b3: bit -> nybble

val all_zero: nb: nybble -> Tot my_bool
let all_zero = function
  | Bits B0 B0 B0 B0 -> T
  | Bits _ _ _ _ -> F

let all_zero_test () : Lemma (all_zero (Bits B1 B0 B1 B0) == F) =
  normalize_term_spec (all_zero (Bits B1 B0 B1 B0))

let all_zero_test' () : Lemma (all_zero (Bits B0 B0 B0 B0) == T) =
  normalize_term_spec (all_zero (Bits B0 B0 B0 B0))

(** ** Numbers *)

(* Peano number (https://en.wikipedia.org/wiki/Peano_axioms) *)
type pnat =
  | O: pnat
  | S: pnat -> pnat

val pred: n: pnat -> Tot pnat
let pred = function
  | O -> O
  | S n' -> n'

let pred_test () : Lemma (pred (S (S O)) = S O) =
  normalize_term_spec (pred (S (S O)))

val minustwo: n: pnat -> Tot pnat
let minustwo = function
  | O -> O
  | S O -> O
  | S (S n') -> n'

let minustwo_test () : Lemma (minustwo (S (S (S (S O)))) = S (S O)) =
  normalize_term_spec (minustwo (S (S (S (S O)))))

val evenb: n: pnat -> Tot my_bool
let rec evenb = function
  | O -> T
  | S O -> F
  | S (S n') -> evenb n'

val oddb: n: pnat -> Tot my_bool
let oddb n = negb (evenb n)

let test_oddb1 () : Lemma (oddb (S O) = T) =
  normalize_term_spec (oddb (S O))

let test_oddb2 () : Lemma (oddb (S (S (S (S O)))) = F) =
  normalize_term_spec (oddb (S (S (S (S O)))))

val plus: a: pnat -> b: pnat -> Tot pnat
let rec plus a b =
  match a with
  | O -> b
  | S a' -> S (plus a' b)

let plus_test () : Lemma (plus (S (S (S O))) (S (S O)) = S (S (S (S (S O))))) =
  normalize_term_spec (plus (S (S (S O))) (S (S O)))

val mul: a: pnat -> b: pnat -> Tot pnat
let rec mul a b =
  match a with
  | O -> O
  | S a' -> plus b (mul a' b)

let mul_test () : Lemma
  (mul (S (S (S O))) (S (S (S O))) = S (S (S (S (S (S (S (S (S O))))))))) =
  normalize_term_spec (mul (S (S (S O))) (S (S (S O))))

val minus: a: pnat -> b: pnat -> Tot pnat
let rec minus a b =
  match a, b with
  | O, _ -> O
  | S _, O -> a
  | S a', S b' -> minus a' b'

val exp: base: pnat -> power: pnat -> Tot pnat
let rec exp base power =
  match power with
  | O -> S O
  | S p -> mul base (exp base p)

(** **** Exercise: 1 star, standard (factorial)

    Recall the standard mathematical factorial function:

       factorial(0)  =  1
       factorial(n)  =  n * factorial(n-1)     (if n>0)

   Translate it into F*.
 *)

assume val factorial: n: pnat -> pnat

let test_factorial () : Lemma (factorial (S (S (S O))) = S (S (S (S (S (S O)))))) =
  admit() // normalize_term_spec (factorial (S (S (S O))))

(** [] *)

val eqb: a: pnat -> b: pnat -> Tot my_bool
let rec eqb a b =
  match a, b with
  | O, O -> T
  | S a', S b' -> eqb a' b'
  | _, _ -> F

val leb: a: pnat -> b: pnat -> Tot my_bool
let rec leb a b =
  match a, b with
  | O, _ -> T
  | S _, O -> F
  | S a', S b' -> leb a' b'

let test_leb1 () : Lemma (leb (S (S O)) (S (S O)) == T) =
  normalize_term_spec (leb (S (S O)) (S (S O)))

let test_leb2 () : Lemma (leb (S (S O)) (S (S (S (S O)))) == T) =
  normalize_term_spec (leb (S (S O)) (S (S (S (S O)))))

let test_leb3 () : Lemma (leb (S (S (S (S O)))) (S (S O)) == F) =
  normalize_term_spec (leb (S (S (S (S O)))) (S (S O)))

(** **** Exercise: 1 star, standard (ltb)

    The ltb function tests natural numbers for less-than,
    yielding a [b]oolean.  Instead of making up a new recursive
    definition for this one, define it in terms of a previously
    defined function. (It can be done with just one previously defined
    function, but you can use two if you want.) *)

assume val ltb: a: pnat -> b: pnat -> my_bool

let test_ltb1 () : Lemma (ltb (S (S O)) (S (S O)) == F) =
  admit() // normalize_term_spec (ltb (S (S O)) (S (S O)))

let test_ltb2 () : Lemma (ltb (S (S O)) (S (S (S (S O)))) == T) =
  admit() // normalize_term_spec (ltb (S (S O)) (S (S (S (S O)))))

let test_ltb3 () : Lemma (ltb (S (S (S (S O)))) (S (S O)) == F) =
  admit() // normalize_term_spec (ltb (S (S (S (S O)))) (S (S O)))

(** [] *)

(** * Proof by Simplification *)

let plus_O_n (n: pnat) : Lemma (ensures (plus O n = n)) = ()

let plus_S_l (n: pnat) : Lemma (ensures (plus (S O) n = S n)) = ()

let mul_O_l (n: pnat) : Lemma (ensures (mul O n = O)) = ()

(** * Proof by Rewriting *)

let plus_id_example (a: pnat) (b: pnat) : Lemma
  (ensures (a = b ==> plus a a = plus b b)) = ()

(** **** Exercise: 1 star, standard (plus_id_exercise) *)
assume val plus_id_exercise: a: pnat -> b: pnat -> c: pnat -> Lemma
  (ensures (a = b ==> b = c ==> plus a b = plus b c))
(** [] *)

val mul_n_O: n: pnat -> Lemma (ensures (O = mul n O))
let rec mul_n_O n =
  match n with
  | O -> ()
  | S n' -> mul_n_O n'

val mul_O_plus: n: pnat -> m: pnat -> Lemma
  (ensures (mul (plus O n) m = mul n m))
let rec mul_O_plus n m =
  match n with
  | O -> ()
  | S n' -> mul_O_plus n' m
