module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M5Assembly
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M5Crit
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M5Co1Cube
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M5Baby

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017


theorem i1016M5Fact_holds : I1016M5Fact :=
  H1016M5.i1016M5Fact_of_parts H1016M5.twoLocalRankCriterion_holds
    H1016M5.co1FiveCubeFacts_holds H1016M5.babyFiveRankFact_holds

end CFSG.LocalAnalysis.GLTheoremA.H1017

end
