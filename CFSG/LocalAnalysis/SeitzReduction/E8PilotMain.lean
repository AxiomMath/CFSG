module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotMainRows

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)
open CFSG.SeitzReduction.F4Pilot (QuadraticFrobenius)


theorem false_of_e8Work_of_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hE7Odd : E7NotOddLieInput) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hFN : E8FieldNeighbourInput)
    (h3 : E8FieldRowStep3Input) (hSCT : E8SwapRowCTInput) (hSU : E8SwapRowUniqueInput)
    (h2 : E8TwoInput) {G : Type} [Group G] [Finite G] {L : Subgroup G} {K₂ : Type} [Field K₂]
    [Finite K₂] [CharP K₂ 2] {σ : K₂ ≃+* K₂} {f : ℕ} (hq : QuadraticFrobenius K₂ σ f)
    (e : L ≃* adjointGroup .E8 (fixSubfield σ)) {t : G} (hw : E8Work L (fixSubfield σ) t f) :
    False := by
  have : CharP (fixSubfield σ) 2 := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · obtain rfl : f = 1 := by have := hw.one_le; omega
    exact h2 G L (fixSubfield σ) e t hw
  · rcases hr8FieldE8_or_hr8SwapE8 hGLS hE7Odd hMinn hMcomp hw hf2 e with hX | hX
    · exact false_of_fieldRow_E8 hFN h3 hq hf2 e hw hX
    · exact false_of_swapRow_E8 hSCT hSU hw hf2 e hX

theorem seitzExclusion_highE8_of_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hE7Odd : E7NotOddLieInput) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hFN : E8FieldNeighbourInput)
    (h3 : E8FieldRowStep3Input) (hSCT : E8SwapRowCTInput) (hSU : E8SwapRowUniqueInput)
    (h2 : E8TwoInput) : SeitzExclusion (HighExceptional .E8) :=
  seitzExclusion_highE8_of_forall fun _ _ _ _ _ _ _ _ _ _ hq e _ hw =>
    false_of_e8Work_of_inputs hGLS hE7Odd hMinn hMcomp hFN h3 hSCT hSU h2 hq e hw

end CFSG.SeitzReduction.E8Pilot
