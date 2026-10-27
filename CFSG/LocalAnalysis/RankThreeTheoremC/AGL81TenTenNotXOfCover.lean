module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTenCfgOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenEightNotX
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenEightNormalizer
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenEightExcl

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem agl81TenTenNotXCfg_of_cover
    (h31 : KFactThreeOne) (h75 : KFactSevenFive) (hR1 : KFactNineThreeListRankOne)
    (hSyl : KFactCaseTwoSylowAut) (hSch : KFactCatalogSchreier) (h74 : AGL81SevenFourTwo)
    (hOutC : KFactOutCyclic) (hR2 : KFactNineThreeRankTwo)
    (hSchF : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (hsec : KFactNineThreeAutSection) (hK342 : TenThirteen.KFactThreeFourTwo)
    (hJ : TenEight.KFactThreeFourPairJShape) (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hNX3 : D1NoXBlock3 G) (hclaim : AGL81TenTenClaimCfg G) (h98 : AGL81NineEightTwo G)
    (h984 : AGL81NineEightFour G) (h101 : AGL81TenOneExists G) (h1031 : AGL81TenThreeOneAt G)
    (h105 : AGL81TenFiveXCfg G) : AGL81TenTenNotXCfg G := by
  intro hS p P M H Q K hd L hL hNL I₀ hI₀
  have hD2 : CFSG.AGLEmbeddingD2.NoXBlockFor G := noXBlockFor_of_setting hNX3 hS
  have hExcl : ∀ m ∈ M, ∀ (q : ℕ) (iK iJ : TauCeti.CFSGIndex),
      TenThirteen.IsThreeFourPair q iK iJ →
      ∀ f : ↥(L.map (MulAut.conj m).toMonoidHom) →* iJ.Group, ¬ Function.Surjective f :=
    fun _ _ _ _ _ hpair f hf =>
      TenEight.false_of_pairJ hJ h85 h93 h984 hD2 hS hd hL hNL hpair f hf
  exact TenEight.not_le_d1PlusCore_of_cover h31 h75 hR1 hSyl hSch h74 hOutC hR2 hSchF hsec hK342
    hclaim h98 h984 h1031 h105 hS hd hL hNL hI₀ hExcl fun m hm =>
      TenEight.normalizer_conj_le_of_not_normal h31 h75 hR2 hK342 h98 h101 h1031 hS hd hL hNL
        hI₀ hExcl hm

end CFSG.LocalAnalysis.RankThreeTheoremC
