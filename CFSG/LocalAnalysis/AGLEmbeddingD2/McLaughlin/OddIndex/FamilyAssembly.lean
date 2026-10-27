module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.FamilyJ1
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.FamilyL2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.Reduction
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.Core

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

set_option linter.unusedSectionVars false


theorem kFactThreeRankOneOvergroupL32_of_L3U3
    (hS : CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactThreeRankOneSimple)
    (h3 : OvergroupL32L3) (hu : OvergroupL32U3) : KFactThreeRankOneOvergroupL32 :=
  kFactThreeRankOneOvergroupL32_of_families hS overgroupL32L2_proved h3 hu overgroupL32J1_proved

theorem kFactLThreeTwoOddIndex_of_L3U3 (hCat : CFSG.AGLEmbedding.CatalogOuterSolvable)
    (hS : CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactThreeRankOneSimple)
    (h3 : OvergroupL32L3) (hu : OvergroupL32U3) : KFactLThreeTwoOddIndex :=
  kFactLThreeTwoOddIndex_of (kFactThreeRankOneOvergroupL32_of_L3U3 hS h3 hu)
    (lThreeTwoCoreOdd_of hCat)

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
