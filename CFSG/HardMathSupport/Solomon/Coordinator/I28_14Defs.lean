module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_5Section

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.ComponentClassification.OutcomeLocal CFSG.Open

section Defs

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

@[expose] def IsTvIrred (G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)) : Prop :=
  (∃ S : Set (LinearMap.GeneralLinearGroup (ZMod 2) U), S.Nonempty ∧
      (∀ t ∈ S, IsF2Transvection t) ∧ G = Subgroup.closure S) ∧
    ∀ W : Submodule (ZMod 2) U,
      (∀ g ∈ G, ∀ w ∈ W, (g : U →ₗ[ZMod 2] U) w ∈ W) → W = ⊥ ∨ W = ⊤

@[expose] def IsMaxElemAbelianIn (p : ℕ) (G A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)) :
    Prop :=
  A ≤ G ∧ IsElemAbelian p A ∧
    ∀ A' : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U), A' ≤ G → IsElemAbelian p A' →
      Nat.card A' ≤ Nat.card A

@[expose] def HasCentralizedConj (p : ℕ)
    (G A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U))
    (t : LinearMap.GeneralLinearGroup (ZMod 2) U) : Prop :=
  ∃ y ∈ G, ∃ E ≤ A, Nat.card A ≤ p * Nat.card E ∧
    ∀ e ∈ E, e * (y⁻¹ * t * y) = (y⁻¹ * t * y) * e

end Defs

end CFSG.HardMathSupport.Solomon.Coordinator
