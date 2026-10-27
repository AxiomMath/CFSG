module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

@[expose] def KFactFi22CentThreeRank : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.AGLEmbedding.IsFi22 K → ∀ T : Sylow 5 K,
    ∃ t ∈ (T : Subgroup K), ∃ t' ∈ (T : Subgroup K), t ≠ 1 ∧ t' ≠ 1 ∧
      ∃ x y : K, x * t = t * x ∧ y * t' = t' * y ∧
        CFSG.Open.IsElemAbelian 3 (Subgroup.closure ({x, y} : Set K)) ∧
        Nat.card (Subgroup.closure ({x, y} : Set K)) = 3 ^ 2

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
