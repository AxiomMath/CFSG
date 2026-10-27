module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenGTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenPairs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenResidueDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenTwoCopies
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenL33

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_mulEquiv (h31 : KFactThreeOne) (hSch : KFactCatalogSchreier)
    (hS : Setting G) {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : AGL81CfgData p P M H Q K)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {I₀ : Subgroup G}
    (hI₀ : I₀ ∈ cZero (H ⊓ L)) (hI : IsTwoPrimeComponent I₀ I₀) {T Y : Type*} [Group T]
    [Group Y] (e : K ≃* Y) (hT : center T = ⊥) (f : I₀ →* T) (hf : Function.Surjective f)
    (hfX : (d1PlusCore p H K).subgroupOf I₀ ≤ f.ker) (hn : ¬ Nat.card T ^ 2 ∣ Nat.card Y) :
    H ⊓ L ≤ normalizer (I₀ : Set G) :=
  le_normalizer_of_not_card_sq_dvd h31 hSch hS hd hL hI₀ hI hT f hf hfX
    (by rwa [Nat.card_congr e.toEquiv])

theorem agl81TenThirteenPerfect_of (h31 : KFactThreeOne) (hSch : KFactCatalogSchreier)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : CFSG.AGLEmbeddingD2.NoXBlockFor G)
    (h984 : AGL81NineEightFour G) (h94 : AGL81NineFourCfg G) (hSU : KFactBlockNoSU38)
    (hG28 : KFactG28RankNotNineFour) (hAut : KFactG28AutCard) (hB : KFactBlockNoL33U35L37He)
    (hPair : KFactThreeFourPairOrders) (hSp62 : AGL81TenThirteenSp62 G)
    (hSp48 : AGL81TenThirteenSp48 G) (hA10 : AGL81TenThirteenA10 G) :
    AGL81TenThirteenPerfect G := by
  intro hS p P M H Q K hpσ hd L hL I₀ hI₀ hI _hnX iK iJ hPair eK fex
  obtain ⟨f, hf, hfX⟩ := fex
  rcases hPair with ⟨rfl, q, hqp, hqe, dK, dJ, hdK, hdJ, hiK, hiJ⟩
    | ⟨rfl, q, hqp, hqe, dK, dJ, hdK, hdJ, hiK, hiJ⟩
    | ⟨rfl, q, hqp, hqe, dK, dJ, hdK, hdJ, hiK, hiJ⟩
    | ⟨rfl, q, hqp, hqe, dK, dJ, hdK, hdJ, hiK, hiJ⟩
    | ⟨rfl, h₁, h₂, hiK, hiJ⟩
    | ⟨rfl, q, hqp, hqe, dJ, hdJ, hiK, hiJ⟩
    | ⟨rfl, q, hqp, hqe, dJ, hdJ, hiK, hiJ⟩
    | ⟨rfl, hiK, hiJ⟩
  ·
    subst iK
    subst iJ
    obtain ⟨e⟩ := eK
    obtain ⟨hcenter, hndvd⟩ := hPair.1 q dK dJ hqp hqe hdK hdJ
    have hN := le_normalizer_of_mulEquiv h31 hSch hS hd hL hI₀ hI e hcenter f hf hfX hndvd
    exact hSp62 hS P M H Q K hd L hL I₀ hI₀ hI hN q dK dJ hqp hqe hdK hdJ ⟨e⟩ f hf hfX
  ·
    subst iK
    subst iJ
    obtain ⟨e⟩ := eK
    obtain ⟨hcenter, hndvd⟩ := hPair.2.1 q dK dJ hqp hqe hdK hdJ
    have hN := le_normalizer_of_mulEquiv h31 hSch hS hd hL hI₀ hI e hcenter f hf hfX hndvd
    exact false_of_g28 h84 h85 h86 h93 hD2 h984 h94 hSU hG28 hAut hS hd hL hI₀ hI hN
      ⟨dK, ⟨q, hqp, hqe, hdK⟩, ⟨e⟩⟩ ⟨q, hqp, hqe, hdJ⟩ f hf
  ·
    subst iK
    subst iJ
    obtain ⟨e⟩ := eK
    exact hSp48 hS P M H Q K hpσ hd L hL I₀ hI₀ hI q dK dJ hqp hqe hdK hdJ ⟨e⟩ f hf hfX
  ·
    subst iK
    subst iJ
    obtain ⟨e⟩ := eK
    obtain ⟨hsimple, horder, hcenter, hndvd⟩ := hPair.2.2.1 q dK dJ hqp hqe hdK hdJ
    have hN := le_normalizer_of_mulEquiv h31 hSch hS hd hL hI₀ hI e hcenter f hf hfX hndvd
    haveI : Finite (CatGroup dJ) := Finite.of_surjective f hf
    haveI : IsSimpleGroup (CatGroup dJ) := hsimple
    exact false_of_l33u35l37he h85 h93 hD2 h984 hB hS hd hL hI₀ hI hN f hf horder
  ·
    subst iK
    subst iJ
    obtain ⟨e⟩ := eK
    exact hA10 hS P M H Q K hd L hL I₀ hI₀ hI ⟨e⟩ f hf hfX
  ·
    subst iK
    subst iJ
    obtain ⟨e⟩ := eK
    obtain ⟨hsimple, horder, hcenter, hndvd⟩ := hPair.2.2.2.1 q dJ hqp hqe hdJ
    have hN := le_normalizer_of_mulEquiv h31 hSch hS hd hL hI₀ hI e hcenter f hf hfX hndvd
    haveI : Finite (CatGroup dJ) := Finite.of_surjective f hf
    haveI : IsSimpleGroup (CatGroup dJ) := hsimple
    exact false_of_l33u35l37he h85 h93 hD2 h984 hB hS hd hL hI₀ hI hN f hf horder
  ·
    subst iK
    subst iJ
    obtain ⟨e⟩ := eK
    obtain ⟨hsimple, horder, hcenter, hndvd⟩ := hPair.2.2.2.2.1 q dJ hqp hqe hdJ
    have hN := le_normalizer_of_mulEquiv h31 hSch hS hd hL hI₀ hI e hcenter f hf hfX hndvd
    haveI : Finite (CatGroup dJ) := Finite.of_surjective f hf
    haveI : IsSimpleGroup (CatGroup dJ) := hsimple
    exact false_of_l33u35l37he h85 h93 hD2 h984 hB hS hd hL hI₀ hI hN f hf horder
  ·
    subst iK
    subst iJ
    obtain ⟨e⟩ := eK
    obtain ⟨hsimple, horder, hcenter, hndvd⟩ := hPair.2.2.2.2.2
    have hN := le_normalizer_of_mulEquiv h31 hSch hS hd hL hI₀ hI e hcenter f hf hfX hndvd
    haveI : Finite (TauCeti.CFSGIndex.sporadic .He).Group := Finite.of_surjective f hf
    haveI : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .He).Group := hsimple
    exact false_of_l33u35l37he h85 h93 hD2 h984 hB hS hd hL hI₀ hI hN f hf horder

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
