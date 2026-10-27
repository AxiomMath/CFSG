module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1RegularMain
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1StageMain
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OddNu

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

section Certificates


theorem u3C1InnerExclusion_of_next (hnext : U3C1NextInput) : U3C1InnerExclusion :=
  u3C1InnerExclusion_of_named u3C1RegularInput u3C1NuInput_holds hnext

theorem u3C1Exclusion_of_outer_next (hO : U3C1OuterInput) (hnext : U3C1NextInput) :
    U3C1Exclusion :=
  u3C1Exclusion_of_outer hO (u3C1InnerExclusion_of_next hnext)

end Certificates

end CFSG.SeitzReduction.RankOne
