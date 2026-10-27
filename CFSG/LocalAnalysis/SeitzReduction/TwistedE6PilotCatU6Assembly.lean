module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCatU6
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCatU6Sporadic
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatEvenInner
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatEvenOuterHolds

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)
open CFSG.SeitzReduction.F4Pilot (centerQuotientAut FixedCentralizerTwoFree)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)
open CFSG.SeitzReduction.UnitaryPilot (CatSUmSporadicAt SUmCatalogueClausesAt SUmOvergroup
  SUmNotOddLieInputAt)

theorem catSUmSporadicAtF_six_of_monster (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) {f : ℕ} (hf : 2 ≤ f) : CatSUmSporadicAtF 6 f :=
  fun _ _ _ hS hna hsp _ hσ _ hD hDm _ =>
    (false_of_sporadic_PSU_six_of_two_le hMinn hMcomp hS hna hsp hσ hf hD hDm).elim

section Clauses

theorem sumCatalogueClausesAtF_six_of_leafInputs (hGLS : GLS3OddLieAutComponentsInput)
    (hX : SUmNotOddLieInputAt 6) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) {f : ℕ} (hf : 2 ≤ f) : SUmCatalogueClausesAtF 6 f :=
  ⟨UnitaryPilot.catSUmAlternating, UnitaryPilot.catSUmEvenInner,
    UnitaryPilot.catSUmEvenOuterAt (by norm_num),
    UnitaryPilot.catSUmOddLieAt_of_inputs hGLS (by norm_num) hX,
    catSUmSporadicAtF_six_of_monster hMinn hMcomp hf, UnitaryPilot.catSUmCovers⟩

end Clauses

end CFSG.SeitzReduction.TwistedE6Pilot
