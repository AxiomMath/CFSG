module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevG2

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

section Core


theorem lieOddRankChevRes_of_core (hG : CFSG.Open.GriessAllModelsStatement)
    (h : LieOddRankChevLinCore ∧ LieOddRankChevUniCore) : LieOddRankChevRes :=
  ⟨h.1, h.2, lieOddRankChevG2_holds hG⟩

end Core

end CFSG.LocalAnalysis.RankThreeUC.S15
