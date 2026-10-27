module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightModule
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.NoOrderNine

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def TightCentreTrivial : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X → TightKP (X ⧸ Subgroup.center X) →
    Odd (Nat.card (Subgroup.center X)) → ¬ 3 ∣ Nat.card (Subgroup.center X) →
      Subgroup.center X = ⊥

end CFSG.AGLEmbeddingD2.McLaughlin
