module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5Inputs

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ABGLocalTools

@[expose] def Foote5FieldCentralizerC : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], FooteSimpleType Y →
    ∀ β : MulAut Y, β * β = 1 → β ∉ innAut5 Y →
      (∃ R : Sylow 2 Y, ∀ r ∈ (R : Subgroup Y), β r = r) →
      ∃ M : Subgroup Y, (∀ m ∈ M, β m = m) ∧
        Nat.card ↥(MonoidHom.eqLocus β.toMonoidHom (MonoidHom.id Y)) ≤ 2 * Nat.card M ∧
        (∀ N : Subgroup Y, N ≤ M → (∀ m ∈ M, ∀ x ∈ N, m * x * m⁻¹ ∈ N) → N ≠ ⊥ →
          ∃ V : Subgroup Y, IsKleinFour V ∧ V ≤ N) ∧
        ∀ α : MulAut Y, (∀ m ∈ M, α m = m) → α = 1 ∨ α = β

end CFSG.ComponentClassification.Foote5
