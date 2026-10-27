module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SevenSwapMain
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatSporadicFourProved

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

theorem linearTwoInput_of_gls3_fiveSix (hGLS : GLS3OddLieAutComponentsInput)
    (h56 : LinearTwoFiveSixInput) : LinearTwoInput :=
  linearTwoInput_of_fiveSix hGLS (fun _ hm => catSLmSporadicAt_of_four_le (by omega)) h56

end CFSG.SeitzReduction.LinearPilot
