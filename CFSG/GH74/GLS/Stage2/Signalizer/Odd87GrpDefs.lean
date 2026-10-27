module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup
open scoped commutatorElement

variable {A : Type} [Group A] [Finite A]

structure Setup412 (p : ℕ) (W X : Subgroup A) (z : A) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  W2 : IsPGroup 2 ↥W
  Xp : IsPGroup p ↥X
  XW : X ≤ normalizer (W : Set A)
  zW : z ∈ normalizer (W : Set A)
  z2 : z * z = 1
  zX : z ∈ normalizer (X : Set A)
  comm : ⁅X, zpowers z⁆ = X
  Cz : ∀ c ∈ W, c * z = z * c → c ∈ normalizer (X : Set A)

structure Part1 (p : ℕ) (W X : Subgroup A) (z : A) : Prop where
  setup : Setup412 p W X z
  comm_eq : ⁅W, X⁆ = W
  ne_bot : W ≠ ⊥
  nonab : ¬ ∀ a ∈ W, ∀ b ∈ W, a * b = b * a
  abel_central : ∀ U : Subgroup A, U ≤ W → (∀ w ∈ W, ∀ u ∈ U, w * u * w⁻¹ ∈ U) →
    X ≤ normalizer (U : Set A) → z ∈ normalizer (U : Set A) →
    (∀ a ∈ U, ∀ b ∈ U, a * b = b * a) → U ≤ centralizer (W : Set A)
  class_two : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ⁅⁅a, b⁆, c⁆ = 1
  X_cent_Z : W ⊓ centralizer (W : Set A) ≤ centralizer (X : Set A)
  CX_le_derived : W ⊓ centralizer (X : Set A) ≤ ⁅W, W⁆

structure Core412 (W X : Subgroup A) (z : A) : Prop where
  nonab : ¬ ∀ a ∈ W, ∀ b ∈ W, a * b = b * a
  Z_eq_derived : W ⊓ centralizer (W : Set A) = ⁅W, W⁆
  Z_eq_fix : W ⊓ centralizer (W : Set A) = W ⊓ centralizer (X : Set A)
  X_cent_Z : X ≤ centralizer ((W ⊓ centralizer (W : Set A) : Subgroup A) : Set A)
  sq_central : ∀ w ∈ W, w * w ∈ W ⊓ centralizer (W : Set A)
  Z_exp2 : ∀ g ∈ W ⊓ centralizer (W : Set A), g * g = 1
  card_le : Nat.card ↥W ≤ Nat.card ↥(W ⊓ centralizer (W : Set A)) *
    Nat.card ↥(W ⊓ centralizer (W : Set A) ⊓ centralizer ({z} : Set A)) ^ 2
  card8 : Nat.card ↥(W ⊓ centralizer (W : Set A) ⊓ centralizer ({z} : Set A)) = 2 →
    Nat.card ↥W = 8

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
