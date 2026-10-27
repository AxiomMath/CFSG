module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Group.Subgroup.Map

public section

namespace CFSG.LargeExtraspecial.S9

open Subgroup

universe u

@[expose] def TIPairInput : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (A : Subgroup G) (y : G),
    (∀ a ∈ A, a * a = 1) →
    (∀ x : G, A ⊓ A.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      A ⊓ A.map (MulAut.conj x).toMonoidHom = A) →
    A ⊓ normalizer (A.map (MulAut.conj y).toMonoidHom : Set G) ≠ ⊥ →
    4 * Nat.card ↥(A ⊓ normalizer (A.map (MulAut.conj y).toMonoidHom : Set G)) ≤ Nat.card A →
    ∀ t ∈ A ⊓ normalizer (A.map (MulAut.conj y).toMonoidHom : Set G), t ≠ 1 →
      ∃ x ∈ A ⊔ A.map (MulAut.conj y).toMonoidHom, x * t * x⁻¹ ∈ A ∧ x * t * x⁻¹ ≠ t

end CFSG.LargeExtraspecial.S9
