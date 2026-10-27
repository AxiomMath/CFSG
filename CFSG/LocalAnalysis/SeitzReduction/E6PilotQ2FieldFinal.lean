module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2FieldMain
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatSporadicFourProved

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open CFSG.Open CFSG.EvenSmallLie
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)


theorem seitzExclusion_highE6_of_gls3 (hGLS : GLS3OddLieAutComponentsInput) :
    SeitzExclusion (HighExceptional .E6) :=
  seitzExclusion_highE6_of_gls3_sporadic hGLS
    (LinearPilot.catSLmSporadicAt_of_four_le (by norm_num))

end CFSG.SeitzReduction.E6Pilot
