module

public import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.Open
public import CFSG.LieType.SeitzGeneration.InnerExHolds

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

theorem gl83NongenerationList_of_componentPCoreTrivial
    (h243 : GL83ComponentPCoreTrivial) : GL83NongenerationList :=
  gl83NongenerationList_of_open CFSG.LieType.SeitzGeneration.seitzExcAnisotropicNotG2ThreePlus_holds
    CFSG.LieType.SeitzGeneration.ExcOuterLeOne.seitzExcOuterCycResiduals_of_core h243

end CFSG.LocalAnalysis.RankFourTheoremC
