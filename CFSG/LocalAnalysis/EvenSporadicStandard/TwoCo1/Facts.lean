module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open Subgroup

variable {G : Type*} [Group G]

@[expose] def HasEighthRoot (L : Subgroup G) (y : G) : Prop := ∃ v ∈ L, v ^ 8 = y

abbrev centIn (L : Subgroup G) (y : G) : Subgroup G := L ⊓ centralizer ({y} : Set G)

@[expose] def InvType (L : Subgroup G) (z : G) (c : ℕ) (y : G) : Prop :=
  y ∈ L ∧ orderOf y = 2 ∧ y ≠ z ∧ ¬ HasEighthRoot L y ∧ Nat.card (centIn L y) = c

structure Co0Facts (L : Subgroup G) (z : G) (c₂ c₃ : ℕ) : Prop where
  classify : ∀ y ∈ L, orderOf y = 2 → y ≠ z →
    Nat.card (centIn L y) = c₂ ∨ Nat.card (centIn L y) = c₃
  pCore_typeC : ∀ y, InvType L z c₃ y →
    z ∈ CFSG.Open.pCoreOf 2 (centIn L y) ∧ CFSG.Open.pCoreOf 2 (centIn L y) ≤ L ∧
    (∀ a ∈ CFSG.Open.pCoreOf 2 (centIn L y), ∀ b ∈ CFSG.Open.pCoreOf 2 (centIn L y),
      a * b = b * a) ∧
    (∀ a ∈ CFSG.Open.pCoreOf 2 (centIn L y), a ^ 2 = 1) ∧
    Nat.card (CFSG.Open.pCoreOf 2 (centIn L y)) = 2 ^ 12 ∧
    L ⊓ centralizer ((CFSG.Open.pCoreOf 2 (centIn L y) : Subgroup G) : Set G) ≤
      CFSG.Open.pCoreOf 2 (centIn L y)
  orbit_typeC : ∀ y, InvType L z c₃ y →
    Nat.card {t : G | t ∈ CFSG.Open.pCoreOf 2 (centIn L y) ∧ InvType L z c₃ t} = 2576 ∧
    ∀ t, t ∈ CFSG.Open.pCoreOf 2 (centIn L y) → InvType L z c₃ t →
      ∃ n ∈ L ⊓ normalizer ((CFSG.Open.pCoreOf 2 (centIn L y) : Subgroup G) : Set G),
        n * y * n⁻¹ = t

end CFSG.EvenSporadicStandard.TwoCo1
