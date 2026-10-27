module

public import CFSG.LocalAnalysis.ComponentClassification.GSLitSchreier
public import CFSG.RankThree.PartOne.SPOR.Final

public section

namespace CFSG.ComponentClassification.GSLit

theorem globallyFirstRankTwoInput_holds :
    GloballyFirstRankTwoInput :=
  globallyFirstRankTwoInput_of_schreier CFSG.RankThree.PartOne.SPOR.schreierFor_catalog

end CFSG.ComponentClassification.GSLit
