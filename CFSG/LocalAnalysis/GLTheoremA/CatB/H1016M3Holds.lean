module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M3Assembly
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M3Co1
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M3Baby
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M5Crit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

section Baby


theorem H1016M3.babyThreeRankFact_holds : H1016M3.BabyThreeRankFact :=
  H1016M3.card_le_of_isElemAbelian_three_B

end Baby

section Monster


theorem i1016M3Fact_holds : I1016M3Fact :=
  H1016M3.i1016M3Fact_of_parts H1016M5.twoLocalRankCriterion_holds
    H1016M3.co1ThreeRankFact_holds H1016M3.co1ThreeSixFixFact_holds
    H1016M3.babyThreeRankFact_holds

end Monster

end CFSG.LocalAnalysis.GLTheoremA.H1017

end
