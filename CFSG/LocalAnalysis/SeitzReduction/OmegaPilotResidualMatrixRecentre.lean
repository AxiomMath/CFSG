module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualMatrixField
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualRigid

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.Quasithin (perfectCore)
open LinearPilot (autFixSubgroup)

section Defs

variable {C : Type*} [Group C] {K : Type*} [Field K]

@[expose] def FieldCoresSeparated (fp : MulAut C →* (K ≃+* K)) : Prop :=
  ∀ α β : MulAut C, α ^ 2 = 1 → fp α ≠ 1 → β ^ 2 = 1 → β ≠ 1 → fp β = 1 →
    IsEmpty (↥(perfectCore (autFixSubgroup α)) ≃* ↥(perfectCore (autFixSubgroup β)))

end Defs

section Plus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

theorem fieldRecentreIn_plus_of_separated (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    (hRT : FieldCoresSeparated (plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn)) :
    FieldRecentreIn (plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn)
      (IsLongRoot (coordinateQuadPlus n K)) := by
  intro α β hα2 hfp hβ2 hβ1 Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hX
  by_cases hfpβ : plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn β = 1
  · exfalso
    exact (hRT α β hα2 hfp hβ2 hβ1 hfpβ).false
      (((perfectCore (autFixSubgroup α)).equivMapOfInjective φ₁ hφ₁).trans
        ((MulEquiv.subgroupCongr hX).trans
          ((perfectCore (autFixSubgroup β)).equivMapOfInjective φ₂ hφ₂).symm))
  · exact fieldRecentre_of_field hK hn hα2 hfp hβ2 hfpβ Γ φ₁ φ₂ hφ₁ hφ₂ hX

end Plus

end CFSG.SeitzReduction.OmegaPilot
