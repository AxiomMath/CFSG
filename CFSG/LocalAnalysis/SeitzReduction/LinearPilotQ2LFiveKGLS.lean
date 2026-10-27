module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveKOdd
public import CFSG.LocalAnalysis.SeitzReduction.GLS3OddHolds

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.LinearPilot

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

section GLS

theorem lFiveSmallKindRankInput_of_sevenFamilies (h7 : ∀ t, LFiveSevenRankFamilyInput t) :
    LFiveSmallKindRankInput :=
  lFiveSmallKindRankInput_of_seven SeitzReduction.gls3OddLieAutComponentsInput h7

end GLS

end CFSG.SeitzReduction.LinearPilot
