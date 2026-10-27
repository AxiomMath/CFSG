module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentTenFourteenOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentIrred
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentMaximal
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentOut
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentFieldOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentNilpOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentJZeroOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentAltSixFixed

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

theorem agl81ElevenElevenRankOneCent_of_cited
    (h74 : AGL81SevenFourTwo) (hOut : KFactOutCyclic)
    (h1014 : AGL81TenFourteenCentRestCfg G) (h10143 : AGL81TenFourteenThreeCfgGen G)
    (h1033 : AGL81TenThreeThreeCasesCfg G) (hKC : KFactCentralThreeClassical)
    (hKL : KFactLinUnitThreeParabolic)
    (hcc : CFSG.LocalAnalysis.RankFourTheoremC.KFactCenterCyclicGeFive) :
    AGL81ElevenElevenRankOneCent G :=
  agl81ElevenElevenRankOneCent_of (agl81TenFourteenCentCfg_of h74 hOut h1014) h10143 h1033
    agl81ElevenElevenJZeroShape_holds
    (kFactStepThreeCentNilp_of_centSylow kFactStepThreeCentSylow_holds) kFactStepThreeIrred_holds
    kFactStepThreeMaximal_holds kFactStepThreeCentSylow_holds kFactStepThreeNormSolv_holds
    kFactFieldAutInvert_holds hKC kFactAltSixFixed_holds hKL hcc

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
