module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidual
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMain

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)

@[expose] def OmegaPlusResidualMatrixInput : Prop :=
  ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (hn : 5 ≤ n), Even f →
      NonFieldCoresRigid (plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn) ∧
        FieldRecentreIn (plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn)
          (IsLongRoot (coordinateQuadPlus n K))

theorem omegaPlusResidualInput_of_matrixInput (h : OmegaPlusResidualMatrixInput) :
    OmegaPlusResidualInput := by
  intro G _ _ L hset n f K _ _ _ hK hf2 hfe hn e t ht hKt _
  obtain ⟨hFR, hRC⟩ := h n f K hK (by omega) hfe
  exact exists_conj_eq_mul_longRoot_twoSided_plus_of_rigid hset (by omega) hK
    ((LinearPilot.four_le_card_iff_two_le hK).2 hf2) e ht hKt hFR hRC

end CFSG.SeitzReduction.OmegaPilot
