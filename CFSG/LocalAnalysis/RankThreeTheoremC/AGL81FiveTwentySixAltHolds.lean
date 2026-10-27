module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81FiveTwentySixAltAsm
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.Closed

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

theorem gnAltFacts_holds :
    CFSG.AGLEmbeddingD2.GN.GNAltFacts :=
  CFSG.AGLEmbeddingD2.GN.gnAltFacts_of_gf2EightFive
    (CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.gf2EightFive_of_b42L42Core
      CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.b42L42Core_holds)
    (CFSG.AGLEmbeddingD2.GN.gnAltRest_of_seven
      (CFSG.AGLEmbeddingD2.GN.gnAltRestSeven_of_threeRank
        CFSG.AGLEmbeddingD2.McLaughlin.A7Six.gnAltSevenThreeRank_proved))

theorem agl81FiveTwentySixAlt_holds :
    AGL81FiveTwentySixAlt :=
  FiveTwentySix.agl81FiveTwentySixAlt_of gnAltFacts_holds aschbacherLocalCGTBlock_proved

end CFSG.LocalAnalysis.RankThreeTheoremC
