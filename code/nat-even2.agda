-- set is type in Agda
data Nat : Set where
  z : Nat
  s : Nat → Nat

-- first definition of even
data Even : Nat → Set where
  even/z : Even z
  even/s : {n : Nat} → Even n → Even (s (s n))

-- second definition of even
-- done this way due to mutual-recursion in definitions
data Odd : Nat → Set
data Even2 : Nat → Set

data Even2 where
  even2/z : Even2 z
  even2/s : ∀ {n : Nat} → Odd n → Even2 (s n)

data Odd where
  odd/s : ∀ {n : Nat} → Even2 n → Odd (s n)

-- even implies even2
even-implies-even2 : ∀ {n : Nat} → Even n → Even2 n
even-implies-even2 even/z = even2/z
even-implies-even2 (even/s n) = even2/s (odd/s (even-implies-even2 n))

-- exercise 1: prove the other direction
even2-implies-even : ∀ {n : Nat} → Even2 n → Even n
even2-implies-even even2/z = even/z
even2-implies-even (even2/s (odd/s n)) = even/s (even2-implies-even n)

-- exercise 2: bogus : nat
-- not sure how to translate this exercise due to how Nat is defined
-- is there a different way to define Nat to allow for this?

-- exercise 3 : bonus
-- prove that every nat is even or odd
data EvenOrOdd : Nat → Set where
  eo/e : ∀ {n : Nat} → Even2 n → EvenOrOdd n
  eo/o : ∀ {n : Nat} → Odd n → EvenOrOdd n

-- prove the following lemma
-- note: in Agda, this was derived automatically, with Twelf I was struggling to
-- understand what I even need to do
eo-succ : ∀ {n : Nat} → EvenOrOdd n → EvenOrOdd (s n)
eo-succ (eo/e x) = eo/o (odd/s x)
eo-succ (eo/o x) = eo/e (even2/s x)

-- then prove the main theorem
every-nat-eo : ∀ (n : Nat) → EvenOrOdd n
every-nat-eo z = eo/e even2/z
every-nat-eo (s n) = eo-succ (every-nat-eo n)

-- exercise 3.5 bonus
-- answer: the lemma was needed to help with the recursive case here otherwise we couldn't convince
-- the termination checker that the result is "smaller"
-- I don't think it's possible without the lemma, but it might be wrong
-- every-nat-eo2 z = eo/e even2/z
-- every-nat-eo2 (s n) = every-nat-eo2 {!!}  -- termination error
