-- pcf.agda
-- λ-calculus in Agda
-- Programming Computable Functions (PCF) is a tiny type system 
-- with primitive recursive function over the inductively-defined
-- naturals

import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open Data.Product
import Data.Unit using (⊤; tt)
import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open Data.Sum
import Data.Empty using (⊥; ⊥-elim)
import Function.Equivalence using (_⇔_)
open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

Id : Set
Id = String
 
infix 5 ƛ_⇒_
infix 5 μ_⇒_
infixl 7 _·_
infix 8 `suc_
infix 9 `_

data Term : Set where
  `_                   : Id → Term
  ƛ_⇒_                 : Id → Term → Term
  _·_                  : Term → Term → Term
  `zero                : Term
  `suc_                : Term → Term
  case_[zero⇒_|suc_⇒_] : Term → Term → Id → Term → Term
  μ_⇒_                 : Id → Term → Term
  
two : Term
two = `suc `suc `zero

data Value : Term → Set where
  V-ƛ    : ∀ {x N} → Value (ƛ x ⇒ N)
  V-zero : Value `zero
  V-suc  : ∀ {V} → Value V → Value (`suc V)

infix 9 _[_:=_]

-- \Gl- is ƛ

-- Substitution does case analysis on the term, and uses the
-- decidable function x ≟ y, which produces either (a) a
-- proof that x ≡ y, or (b) a proof that x ≢ y
_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _ = V
... | no _  = ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _ = ƛ x ⇒ N
... | no  _ = ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ] = L [ y := V ] · M [ y := V ]
(`zero) [ y := V ] = `zero
(`suc M) [ y := V ] = `suc M [ y := V ]
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _  = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no _   = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _ = μ x ⇒ N
... | no  _ =  μ x ⇒ N [ y := V ]



-- Some example terms

twoᶜ : Term
twoᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

plusᶜ : Term
plusᶜ =  ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
         ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")

_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ]
      ≡ ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
_ = refl

-- ↠  U+21A0  RIGHTWARDS TWO HEADED ARROW (\rr-)
-- ξ is \xi 

infix 4 _⟶_ 

data _⟶_ : Term → Term → Set where
  ξ-·₁ : ∀ {L L′ M} → L ⟶ L′ → L · M ⟶ L′ · M
  ξ-·₂ : ∀ {V M M′} → Value V → M ⟶ M′ → V · M ⟶ V · M′
  β-ƛ : ∀ {x N V} → Value V → (ƛ x ⇒ N) · V ⟶ N [ x := V ]
  ξ-suc : ∀ {M M′} → M ⟶ M′ → `suc M ⟶ `suc M′
  ξ-case : ∀ {x L L′ M N} → L ⟶ L′ → case L [zero⇒ M |suc x ⇒ N ] ⟶ case L′ [zero⇒ M |suc x ⇒ N ]
  β-zero : ∀ {x M N} → case `zero [zero⇒ M |suc x ⇒ N ] ⟶ M
  β-suc : ∀ {x V M N} → Value V → case `suc V [zero⇒ M |suc x ⇒ N ] ⟶ N [ x := V ] 
  β-μ : ∀ {x M} → μ x ⇒ M ⟶ M [ x := μ x ⇒ M ]

infix 2 _↠_
infix 1 begin_
infixr 2 _⟶⟨_⟩_
infix 3  _∎ 

data _↠_ : Term → Term → Set where
 _∎ : ∀ M → M ↠ M
 step⟶ : ∀ L {M N} → M ↠ N → L ⟶ M → L ↠ N

pattern _⟶⟨_⟩_ L L⟶M M↠N = step⟶ L M↠N L⟶M

begin_ : ∀ {M N}
  → M ↠ N
    ------
  → M ↠ N
begin M↠N = M↠N


-- confluence and the diamond properties (unproven here!)

postulate
  confluence : ∀ {L M N}
    → ((L ↠ M) × (L ↠ N))
      --------------------
    → ∃[ P ] ((M ↠ P) × (N ↠ P))

  diamond : ∀ {L M N}
    → ((L ⟶ M) × (L ⟶ N))
      --------------------
    → ∃[ P ] ((M ↠ P) × (N ↠ P))


-- A simple type system! 

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type

-- Contexts are association lists.
-- ⦂  U+2982  Z NOTATION TYPE COLON (\:2)

infixl 5 _,_∶_

data Context : Set where
  ∅      : Context
  _,_⦂_  : Context → Id → Type → Context

-- Context lookup is defined via a judgement:
-- ∋  U+220B  CONTAINS AS MEMBER (\ni)
-- Γ ∋ x ⦂ A 
-- 
-- This is a decidable relation. We define proofs as follows. 

infix 4 _∋_⦂_ 

data _∋_⦂_ : Context → Id → Type → Set where
  Z : ∀ {Γ x A} → Γ , x ⦂ A ∋ x ⦂ A
  S : ∀ {Γ x y A B} → x ≢ y → Γ ∋ x ⦂ A → Γ , y ⦂ B ∋ x ⦂ A

-- Using S directly requires a proof that x ≢ y, so instead we
-- use a "smart constructor" which provides this for us.
-- (I copied this one from the book.. But it makes sense..)
S′ : ∀ {Γ x y A B}
   → {x≢y : False (x ≟ y)}
   → Γ ∋ x ⦂ A
     ------------------
   → Γ , y ⦂ B ∋ x ⦂ A

S′ {x≢y = x≢y} x = S (toWitnessFalse x≢y) x


-- Next: define the typing judgement! 

