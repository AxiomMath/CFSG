module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1StageInd
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1StageTorus

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

section Certificates

theorem u3C1InnerExclusion_of_named (hreg : U3C1RegularInput) (hnu : U3C1NuInput)
    (hnext : U3C1NextInput) : U3C1InnerExclusion :=
  u3C1InnerExclusion_of_inputs hreg u3C1TorusFullInput hnu hnext

end Certificates

end CFSG.SeitzReduction.RankOne
