module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisCaseFor

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

@[expose] def D2HSFiveNonBorel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D2Global G → D1For G →
    ∀ (P : Sylow 5 G) (M A H R : Subgroup G), D2Escape 5 P M A H R → D2EscapeMax 5 P M R →
    5 ∈ GLBBetaFour G →
    ∀ (Rbar : Sylow 5 (H ⧸ primeComplementCore (G := H) 5))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) 5)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5)) →
      D2AlmostSimple 5 (H ⧸ primeComplementCore (G := H) 5) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5))) K →
      Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .HS).Group) →
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5)) ≠
        Subgroup.normalizer (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 5)) :
          Set (H ⧸ primeComplementCore (G := H) 5))) →
      False

theorem d2HeisBorelFor_hs_five (hloc : D2HeisLocalEqAt (.sporadic .HS) fun p => p = 5)
    (hU : D2HSFiveNonBorel) {G : Type} [Group G] [Finite G] (hglob : D2Global G) (hD1 : D1For G)
    {P : Sylow 5 G} {M A R : Subgroup G} (hmax : D2EscapeMax 5 P M R)
    (hβ : 5 ∈ GLBBetaFour G) : D2HeisBorelFor 5 P M A R (.sporadic .HS) :=
  fun H hesc Rbar K hRbar hK he => hloc.heisBorel rfl hK he (by
    by_contra hne
    exact hU G hglob hD1 P M A H R hesc hmax hβ Rbar K hRbar hK he hne)

end CFSG.AGLEmbeddingD2
