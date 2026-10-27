module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2HSFive3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveOver

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

variable {G : Type} [Group G] [Finite G]

@[expose] def D2HSFiveCaseTwo3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → TheoremD1 G → ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M → D2FullCoreAt G M →
    D2ThreeClauseAt G M → ∀ p ∈ rankThreeSigmaA G, p = 5 → ∀ (P : Sylow p G) (A H R : Subgroup G),
    IsCoreMaxLocal p P M → D2Escape p P M A H R → D2EscapeMax p P M R →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .HS).Group) →
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) ≠
        Subgroup.normalizer ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) :
          Set (H ⧸ primeComplementCore (G := H) p)) →
      ∀ L : Subgroup G, IsTwoPrimeComponent M L → L ≤ H ⊓ M → ¬ L ≤ GLBPrimeCore p H → False

theorem d2HSFiveNonBorel3_of_caseTwo (hHS : KFactHSFiveOver)
    (hloc : D2HeisLocalEqAt (.sporadic .HS) fun p => p = 5)
    (hα : KFactThreeOrFiveDvd) (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hX : D1NoXBlock3 G)
    (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hF : KFactBlockFiveHeisInner) (hII : D2HSFiveCaseTwo3 G) :
    D2HSFiveNonBorel3 G := by
  intro hS hD1' M hM hfc hthree p hp hp5 P A H R hMP hesc hmax Rbar K hRbar hK he hne
  subst hp5
  exact false_of_hsFiveNonBorel hHS hloc hα hSch h84 h85 h86 h93 hK2 hC3 hK5 hF
    (aglGlobal_of_setting hS) (d1For_of_setting hS) (noXBlockFor_of_setting hX hS) hesc hRbar hK
    he hne fun L hL2 hLK hLN =>
      hII hS hD1' M hM hfc hthree 5 hp rfl P A H R hMP hesc hmax Rbar K hRbar hK he hne L hL2 hLK
        hLN

end CFSG.LocalAnalysis.RankThreeTheoremC
