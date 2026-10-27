module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5Inputs

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ABGLocalTools

@[expose] def Foote5FieldCentralizer : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], FooteSimpleType Y →
    (∀ β : MulAut Y, β * β = 1 → β ∉ innAut5 Y →
      (∃ R : Sylow 2 Y, ∀ r ∈ (R : Subgroup Y), β r = r) →
        ∃ X : Subgroup Y, (∀ x ∈ X, β x = x) ∧ Nonempty (X ≃* alternatingGroup (Fin 4))) ∧
    ∀ W : Subgroup Y, IsKleinFour W → ∀ γ : MulAut Y, (∀ w ∈ W, γ w ∈ W) →
      (∀ w ∈ W, γ w = w → w = 1) →
      ∀ E : Subgroup (MulAut Y), (∀ α ∈ E, α * γ = γ * α ∧ ∀ w ∈ W, α w = w) →
        ¬ IsKleinFour E

end CFSG.ComponentClassification.Foote5
