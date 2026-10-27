module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

@[expose] def KFactA6TwoSignalizer : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsRankThreeA6 K → ∀ (T : Sylow 3 K),
    ∀ u ∈ (T : Subgroup K), orderOf u = 3 →
      ⊤ ≤ rankThreeGamma 1 3 (T : Subgroup K) ⊔
        sSup {V : Subgroup K | IsPGroup 2 V ∧ u ∈ normalizer (V : Set K)}

@[expose] def A6SylowData : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsRankThreeA6 K → ∀ (T : Sylow 3 K),
    IsElemAbelian 3 (T : Subgroup K) ∧ Nat.card (T : Subgroup K) = 3 ^ 2 ∧
    ∀ Y : Subgroup K, normalizer ((T : Subgroup K) : Set K) ≤ Y →
      Y = normalizer ((T : Subgroup K) : Set K) ∨ Y = ⊤

@[expose] def A6BorelCore : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal →
    centralizer (K : Set X) = ⊥ → IsRankThreeA6 ↥K →
    ∀ T : Subgroup X, T ≤ K → IsSylowOf 3 T K →
      rankThreePrimeCore 3 (normalizer (T : Set X)) = ⊥

end CFSG.LocalAnalysis.RankThreeTheoremC
