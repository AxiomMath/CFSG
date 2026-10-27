module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Port3Amalgam
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Port3Only
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Port3Conf
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Port3Strong

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

variable {G : Type} [Group G] [Finite G]

theorem d2L34BetaResidue3_of_mside
    (hK : D2KFactLeaves)
    (hrows : ∀ s p, (s, p) ∈ d2SporadicRows3 → D2VacuousAt (.sporadic s) p)
    (hT3 : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits → D2VacuousAt (.lie d) 3)
    (hM11 : KFactM11Three) (hM11I : KFactM11ThreeIrr) (hO : KFactL34Outer) (hI : KFactL34Inner)
    (hNO : KFactL34NotOrthogonal) (hK4 : KFactSylowThreeAbelian)
    (hS3 : D2PairStrongThree3Comp G) (hMS : D2L34BetaMSide3 G) : D2L34BetaResidue3 G := by
  intro hS hD1 M hM ha hb P A H R hp hMP hesc hmax d hd Rbar K hRbar hK' he hAK hC htwo hNT hch
  have hc : D2L34BetaConf3 d P M A H R Rbar K :=
    ⟨hd, hesc, hmax, hRbar, hK', he, hAK, hC, htwo, hNT, hch⟩
  have hOnly : D2OnlyL34At P M :=
    d2OnlyL34At3_of_pairStrongComp hK hrows hT3 hM11 hM11I hK4 hS3 hS hD1 hM ha hb hp hMP
  have hAll : D2L34AllResidue3 P M :=
    d2L34AllResidue3_of_onlyL34At hO hI hNO hK.catalogSchreier hK4 hK.eightFour hK.nineThree
      hK.noXBlock3 hS3 hS hD1 hM ha hb hp hMP hOnly
  obtain ⟨hsolv, hside⟩ := hMS hS hD1 M hM ha hb P A H R hp hMP d Rbar K hc hAll
  have hstr : GLBStronglyEmbedded 3 M := by
    by_cases hs : Group.IsSolvable M
    · exact hsolv hs
    · exact hb.stronglyEmbedded_of_not_isSolvable hS hM hp hMP hs
  exact d2L34BetaConf3_false (aglGlobal_of_setting hS) (d1At_of_theoremD1 hD1 hp) hc hAll hstr
    (hside hstr)

end CFSG.LocalAnalysis.RankThreeTheoremC
