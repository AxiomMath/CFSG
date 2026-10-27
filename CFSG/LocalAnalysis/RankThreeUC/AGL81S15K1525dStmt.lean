module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsSmall

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding
open KFactsSmall

@[expose] def K1525dCore : Prop :=
  ∀ (L : Type) [Group L] [Finite L], (Nonempty (L ≃* alternatingGroup (Fin 8)) ∨ IsL5Two L) →
    ∀ S₀ A₁ A₂ : Subgroup L, CFSG.QuasithinUnique.IsSylowTwoOf S₀ ⊤ →
      (∀ P : Subgroup L, IsMinOverBorel ⊤ S₀ P →
        pElementSubgroup 2 P ≤ A₁ ∨ pElementSubgroup 2 P ≤ A₂) →
      CFSG.Open.pRank 3 A₁ ≤ 1 → CFSG.Open.pRank 3 A₂ ≤ 1 →
      IsL3TwoModO2 A₁ ∨ IsL3TwoModO2 A₂

end CFSG.LocalAnalysis.RankThreeUC.S15
