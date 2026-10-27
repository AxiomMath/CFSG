module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenJZero
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenParabolicOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenFourteenThreeCfgGenOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeXCfgOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenCfgNoN2
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSixCfgOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenFourL34NoRem
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81L34ThreeRankTwoProof

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem agl81ElevenElevenRankTwoCfg_of_reduced_noRem (hD : SubnormalSUThreeTwoDetermined)
    (h9 : AGL81NineCompetitorQ G)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : NoXBlockFor G) (h1033 : AGL81TenThreeThreeCfg G)
    (hN1 : TenThreeThree.AGL81ElevenThreeInspectionCfg G) (h93r : AGL81NineThreeRankCfg G)
    (h1013 : AGL81TenThirteenAt G) (h106 : AGL81TenSixX G) (h1062 : AGL81TenSixTwelveCfg G)
    (h1031 : AGL81TenThreeOneAt G) (h10C : AGL81TenOneCZero G) (h91 : AGL81TenNineOneCfg G)
    (h9N : AGL81NineThreeNormalCfg G)
    (h94 : AGL81NineFourCfg G) (hKI : KFactNineFourSylowIrred)
    (hPar : AGL81ElevenElevenParabolicGen G) (h2 : AGL81TenFourteenTwoPerfectA5 G)
    (h101 : AGL81TenOneNoAFiveCfg G) : AGL81ElevenElevenRankTwoCfg G :=
  agl81ElevenElevenRankTwoCfg_of
    (agl81ElevenSevenCfg_of_noN2 hCGT hD2 h1033 hN1 (agl81NineThreeXCfg_of h9) h93r h1013 h106
      h1062 h1031 h10C h91)
    (agl81ElevenSevenFourL34_of_noRem G hD h9N h1013 h93r h1062 h1031) (agl81NineThreeXCfg_of h9)
    h94 hKI hCGT hD2 h1033 hN1 h1031 h10C h91 hPar (agl81TenFourteenThreeCfgGen_of_A5 h2 h101)

theorem agl81ElevenFiveAt_of_reducedNA_noRem (hD : SubnormalSUThreeTwoDetermined)
    (hRk1 : AGL81ElevenElevenRankOneJZeroCfg G)
    (hC : AGL81TenThreeThreeCasesCfg G) (hKP : TenThreeThree.KFactParabolicIrredCentralNA)
    (h9 : AGL81NineCompetitorQ G) (h98 : AGL81NineEightTwo G) (h1010 : AGL81TenTenCfg G)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : NoXBlockFor G) (h1033 : AGL81TenThreeThreeCfg G)
    (hN1 : TenThreeThree.AGL81ElevenThreeInspectionCfg G) (h93r : AGL81NineThreeRankCfg G)
    (h1013 : AGL81TenThirteenAt G) (h106 : AGL81TenSixX G) (h1062 : AGL81TenSixTwelveCfg G)
    (h1031 : AGL81TenThreeOneAt G) (h10C : AGL81TenOneCZero G) (h91 : AGL81TenNineOneCfg G)
    (h9N : AGL81NineThreeNormalCfg G)
    (h94 : AGL81NineFourCfg G) (hKI : KFactNineFourSylowIrred)
    (h2 : AGL81TenFourteenTwoPerfectA5 G) (h101 : AGL81TenOneNoAFiveCfg G)
    (hKC : KFactNineThreeComponentL34) : AGL81ElevenFiveAt G :=
  agl81ElevenFiveAt_of_jZero (agl81ElevenSixCfg_of h1010 h91 h10C)
    (agl81ElevenElevenCfg_of (agl81ElevenSevenCfgThree_of h1031 h10C h91 h93r h1013 h106 h1062)
      (agl81NineThreeXCfg_of h9) h1033 (agl81ElevenElevenParabolic_of_na hC hKP h10C h91)
      (agl81TenFourteenThreeCfg_of
        (agl81TenFourteenTwoThree_of_perfect (agl81TenFourteenTwoPerfect_of_A5 h2)))
      h10C h91 h1031)
    (agl81ElevenElevenOtherJZeroCfg_of
      (agl81ElevenElevenRankTwoCfg_of_reduced_noRem hD h9 hCGT hD2 h1033 hN1 h93r h1013 h106
        h1062 h1031 h10C h91 h9N h94 hKI (agl81ElevenElevenParabolicGen_of_na hC hKP h10C h91) h2
        h101)
      hRk1)
    h98 h9 hCGT hD2 h1033 hKC kFactL34ThreeRankTwo

end CFSG.LocalAnalysis.RankThreeTheoremC
