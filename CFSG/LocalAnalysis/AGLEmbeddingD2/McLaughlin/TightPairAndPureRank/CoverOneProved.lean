module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneFinal
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem kFactParabolicCoverOne_proved :
    KFactParabolicCoverOne :=
  kFactParabolicCoverOne_of_griess
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
