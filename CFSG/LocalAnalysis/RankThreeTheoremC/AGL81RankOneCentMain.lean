module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentAltTenCase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem agl81ElevenElevenRankOneCent_of
    (h1014 : AGL81TenFourteenCentCfg G) (h10143 : AGL81TenFourteenThreeCfgGen G)
    (h1033 : AGL81TenThreeThreeCasesCfg G) (hJ0 : AGL81ElevenElevenJZeroShape G)
    (hI1 : KFactStepThreeCentNilp) (hI2 : KFactStepThreeIrred) (hI4 : KFactStepThreeMaximal)
    (hI5 : KFactStepThreeCentSylow) (hI6 : KFactStepThreeNormSolv)
    (hFld : KFactFieldAutInvert) (hKC : KFactCentralThreeClassical) (hKA : KFactAltSixFixed)
    (hKL : KFactLinUnitThreeParabolic)
    (hcc : CFSG.LocalAnalysis.RankFourTheoremC.KFactCenterCyclicGeFive) :
    AGL81ElevenElevenRankOneCent G := by
  intro hS p P M H Q K hd _ hKs _ _ hKn L hL hLn _ hJX hX1 hpJ W y a z _ hWH _ hzW hzo hzc _ _
    hyl hyo hW haW hao haout hAJ hZL _ b hb hbZ
  by_contra hC
  by_cases hA : Nonempty (↥(d1KBar p M (Subgroup.centralizer ({b} : Set G))) ≃*
    alternatingGroup (Fin 10))
  · exact false_of_altTen hS h1014 h10143 hJ0 hI2 hI5 hFld hcc hd hKs hKn hL hLn hJX hX1 hpJ hWH
      hzW hzo hzc hyl hyo haW hao haout (hW a haW haout) hAJ hZL hb hbZ hC hA
  · exact false_of_not_altTen hS h1014 h10143 h1033 hJ0 hI1 hI2 hI4 hI5 hI6 hFld hKC hKA hKL hd
      hKs hKn hL hLn hJX hX1 hpJ hWH hzW hzo hzc hyl hyo haW hao haout (hW a haW haout) hAJ hZL
      hb hbZ hC (not_nonempty_iff.mp hA)

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
