module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L2Data

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding

@[expose] def D2BlocksCentralized : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D2Global G → D1For G →
    ∀ (p : ℕ) [Fact p.Prime] (M H R X : Subgroup G),
    D2L2Data p M H R X → 5 ≤ p → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      barM M X ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))

end CFSG.AGLEmbeddingD2
