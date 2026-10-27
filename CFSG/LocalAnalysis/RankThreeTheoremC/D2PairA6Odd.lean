module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairA6Ctx
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.StrongThreeAutomizer
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairOddIndex

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique

theorem PairCtx3.transitive_of_oddIndex {G : Type} [Group G] [Finite G] {P : Sylow 3 G}
    {M A H R : Subgroup G} (hK : CFSG.AGLEmbeddingD2.McLaughlin.KFactStrongThreeAutomizer)
    (hctx : PairCtx3 P M A H R) (hodd : ¬ 2 ∣ (H ⊓ M).relIndex H) :
    IsElemAbelian 3 R ∧ Nat.card R = 9 ∧
      TransitiveOnNonidentity (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) R :=
  CFSG.AGLEmbeddingD2.McLaughlin.transitive_of_oddIndex_of_pair hK hctx.pair hctx.esc hctx.strong
    hodd

end CFSG.LocalAnalysis.RankThreeTheoremC
