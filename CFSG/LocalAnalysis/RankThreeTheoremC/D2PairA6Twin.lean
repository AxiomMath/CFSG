module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairA6Ctx
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.NormalizerEscape

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2.McLaughlin

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M A H R : Subgroup G}

theorem PairCtx3.exists_twoGroup_of_evenIndex (hctx : PairCtx3 P M A H R)
    (hev : 2 ∣ (H ⊓ M).relIndex H) :
    ∃ T : Subgroup G, IsPGroup 2 T ∧ pCoreOf 2 M ≤ T ∧
      ¬ Subgroup.normalizer (T : Set G) ≤ M ∧ IsSylowTwoOf T (H ⊓ M) :=
  hctx.pair.exists_twoGroup_of_evenIndex hev

end CFSG.LocalAnalysis.RankThreeTheoremC
