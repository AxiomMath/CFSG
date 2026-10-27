module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatSporadicThreeProved
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34ONOuter

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)

section SuzInput

theorem suzOuterL34Input_holds : SuzOuterL34Input := by
  intro S _ _ ⟨e⟩ σ _ _ hcard D hD hfree
  exact SporadicRefine.suz_not_lieModel_psl_three_two e hcard hD hfree

end SuzInput

section ONInput

theorem onOuterL34Input_holds : ONOuterL34Input := by
  intro S _ _ ⟨e⟩ σ hσ hout D _ hfree
  exact SporadicRefine.on_outer_not_lieModel_psl_three_two e hσ hout hfree

end ONInput

section Clause

theorem catSLmSporadicAt_three : CatSLmSporadicAt 3 :=
  catSLmSporadicAt_three_of_outer suzOuterL34Input_holds onOuterL34Input_holds

end Clause

end CFSG.SeitzReduction.LinearPilot
