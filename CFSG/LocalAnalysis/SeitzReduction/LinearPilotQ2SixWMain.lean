module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixWMove
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatSporadicFourProved
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixWSmall

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.LinearPilot

open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

theorem linearTwoSmallKindAtInput_six_of_rank (hrk : SixSmallKindRankInput) :
    LinearTwoSmallKindAtInput 6 :=
  linearTwoSmallKindAtInput_six_of linearTwoWOneAtInput_six hrk

section Main

theorem slmCatalogueClausesAt_five_of_gls3 (hGLS : GLS3OddLieAutComponentsInput) :
    SLmCatalogueClausesAt 5 :=
  slmCatalogueClausesAt_of_gls3_sporadic (by norm_num) hGLS
    (catSLmSporadicAt_of_four_le (by norm_num))

end Main

end CFSG.SeitzReduction.LinearPilot
