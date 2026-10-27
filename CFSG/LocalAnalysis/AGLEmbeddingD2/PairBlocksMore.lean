module

import CFSG.LocalAnalysis.AGLEmbedding.TwoLocalPairBlockRank
public import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Pair

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

namespace AGLPair

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R : Subgroup G}

theorem relIndex_le_pRank_three (h : AGLPair p M H R)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {A : Subgroup G} (hAK : A ≤ H ⊓ M) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    (A ⊓ Subgroup.normalizer (L : Set G)).relIndex A ≤ Open.pRank 3 (H ⊓ M) :=
  h.toTwoLocalPair.relIndex_le_pRank_three hB3 hAK hL

end AGLPair

end CFSG.AGLEmbeddingD2
