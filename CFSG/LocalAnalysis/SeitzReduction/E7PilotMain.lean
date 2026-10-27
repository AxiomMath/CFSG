module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotMainRows

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)
open CFSG.SeitzReduction.F4Pilot (QuadraticFrobenius)


theorem false_of_e7Work_of_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hXodd : OmegaPilot.OmegaNotOddLieInputAt 6) (hSpor : OmegaPilot.CatOmegaSporadicAt 6)
    (hFam : E7FieldRowFamilyInput) (hSCT : E7SwapRowCTInput) (hSU : E7SwapRowUniqueInput)
    (h2 : E7TwoInput) {G : Type} [Group G] [Finite G] {L : Subgroup G} {K₂ : Type} [Field K₂]
    [Finite K₂] [CharP K₂ 2] {σ : K₂ ≃+* K₂} {f : ℕ} (hq : QuadraticFrobenius K₂ σ f)
    (e : L ≃* adjointGroup .E7 (fixSubfield σ)) {t : G} (hw : E7Work L (fixSubfield σ) t f) :
    False := by
  have : Finite (fixSubfield σ) := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  have : CharP (fixSubfield σ) 2 := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · obtain rfl : f = 1 := by have := hw.one_le; omega
    exact h2 G L (fixSubfield σ) e t hw
  · rcases hr8FieldE7_or_hr8SwapE7_of_inputs hGLS hXodd hSpor hw hf2 e with hX | hX
    · exact false_of_fieldRow_E7 hFam hq hf2 e hw hX
    · exact false_of_swapRow_E7 hSCT hSU hw hf2 e hX

theorem seitzExclusion_highE7_of_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hXodd : OmegaPilot.OmegaNotOddLieInputAt 6) (hSpor : OmegaPilot.CatOmegaSporadicAt 6)
    (hFam : E7FieldRowFamilyInput) (hSCT : E7SwapRowCTInput) (hSU : E7SwapRowUniqueInput)
    (h2 : E7TwoInput) : SeitzExclusion (HighExceptional .E7) :=
  seitzExclusion_highE7_of_forall fun _ _ _ _ _ _ _ _ _ _ hq e _ hw =>
    false_of_e7Work_of_inputs hGLS hXodd hSpor hFam hSCT hSU h2 hq e hw

end CFSG.SeitzReduction.E7Pilot
