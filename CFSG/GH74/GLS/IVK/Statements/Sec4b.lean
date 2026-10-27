module

public import CFSG.GH74.GLS.IVK.Defs2

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def IVK_4_1_R_L3 : Prop :=
  ∀ (J : Type) [Group J] [Finite J] (p n : ℕ), p.Prime → p ≠ 2 →
    (IsSLnEps 3 J 1 (p ^ n) ∨ IsLnEps 3 J 1 (p ^ n)) →
      ∀ z : J, orderOf z = 2 → ∀ X : Subgroup J, X ≤ centralizer ({z} : Set J) → IsPGroup p ↥X →
        Nat.card ↥X = p ^ n →
          ∃ R : Subgroup J, R = CFSG.Open.pCoreOf p (centralizer (X : Set J)) ∧ IsPGroup p ↥R ∧ X ≤ R ∧
            R ≤ centralizer (X : Set J) ∧ Nat.card ↥R = (p ^ n) ^ 3 ∧
            (∀ r ∈ R, (∀ s ∈ R, r * s = s * r) → r ∈ X) ∧ X ≤ ⁅R, R⁆ ∧ (∀ r ∈ R, ∀ s ∈ R, ⁅r, s⁆ ∈ X) ∧
            (∀ r ∈ R, z * r * z⁻¹ * r ∈ X)

end CFSG.GH74.GLS.IVK
