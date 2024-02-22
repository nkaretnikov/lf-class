data Nat : Set where
  z : Nat
  s : Nat → Nat

max : Nat → Nat → Nat
max z m = m
max n z = n
max (s n) (s m) = max n m

--------------------------------------------------------------------------------
-- extrinsic encoding
--------------------------------------------------------------------------------
data Tree : Set where
  leaf : Tree
  node : Tree → Tree → Tree

height : Tree → Nat
height leaf = z
height (node l r) = s (max (height l) (height r))

data Bool : Set where
  false true : Bool

_==_ : Nat → Nat → Bool
z   == z   = true
s n == s m = n == m
_   == _   = false

_and_ : Bool → Bool → Bool
true and true = true
_ and _ = false

-- define what it means for a tree to be balanced
balanced : Tree → Bool
balanced leaf = true
balanced (node l r) = (height l) == (height r)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

-- step by step
fail-long : balanced (node leaf (node leaf leaf)) ≡ false
fail-long =
  begin
    balanced (node leaf (node leaf leaf))
  ≡⟨⟩
    (height leaf == height (node leaf leaf))
  ≡⟨⟩
    z == s (max (height leaf) (height leaf))
  ≡⟨⟩
    z == s (max z z)
  ≡⟨⟩
    z == s z
  ≡⟨⟩
    false
  ∎

-- auto
fail : balanced (node leaf (node leaf leaf)) ≡ false
fail = refl

sol : balanced (node (node leaf leaf) (node leaf leaf)) ≡ true

sol = refl

--------------------------------------------------------------------------------
-- intrinsic encoding, being balanced is part of the type def'n
--------------------------------------------------------------------------------
data BBT : Nat → Set where
  b-leaf : BBT z
  b-node : {n : Nat} → BBT n → BBT n → BBT (s n)

bbt2tree : {n : Nat} → BBT n → Tree
bbt2tree b-leaf = leaf
bbt2tree (b-node l r) = node (bbt2tree l) (bbt2tree r)

-- open import Data.Product renaming (_×_ to _∧_)

bbt-n : ∀ {n : Nat} → (bbt : BBT n) -> Nat
bbt-n {n} _ = n

n-bbt : ∀ {n : Nat} → BBT n
n-bbt {z} = b-leaf
n-bbt {s n} = b-node {n} n-bbt n-bbt

-- prove that Trees are equiv to n-Trees with an index being part of the tree height


height-bbt : ∀ {n : Nat} → (bbt : BBT n) → height (bbt2tree bbt) ≡ n
height-bbt b-leaf = refl
height-bbt (b-node l r) = {!!}
-- n -> bbt -> tree
-- type erasure doesn't work?
-- is there a trick

bbt-balanced : ∀ {n : Nat} {bbt : BBT n} → balanced (bbt2tree bbt) ≡ true
bbt-balanced {z} {b-leaf} = refl
bbt-balanced {s n} {b-node l r} =
-- { ⟨ bbt-balanced {n} {l} , bbt-balanced {n} {r} ⟩ }
-- need to translate this to smth that can use refl. eta? see plfa
   begin
     balanced (bbt2tree (b-node l r))
   ≡⟨⟩ balanced (node (bbt2tree l) (bbt2tree r))
   ≡⟨⟩ height (bbt2tree l) == height (bbt2tree r)
   ≡⟨⟩ {!!}

