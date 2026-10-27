module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreLinMain
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreUniMain
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMatLin
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMatUni

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem lieOddRankChevLinCore_holds (hG : CFSG.Open.GriessAllModelsStatement) :
    LieOddRankChevLinCore :=
  lieOddRankChevLinCore_of_matrix linCoreMatrix hG

theorem lieOddRankChevUniCore_holds (hG : CFSG.Open.GriessAllModelsStatement) :
    LieOddRankChevUniCore :=
  lieOddRankChevUniCore_of_matrix uniCoreMatrix hG

end CFSG.LocalAnalysis.RankThreeUC.S15
