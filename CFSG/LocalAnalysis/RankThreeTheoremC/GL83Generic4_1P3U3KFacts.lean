module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

@[expose] def KFactU3TwoSignalizer : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsRankThreeU3 K → ∀ (T : Sylow 3 K),
    ∀ u ∈ ((center ↥(T : Subgroup K)).map (T : Subgroup K).subtype), orderOf u = 3 →
      ⊤ ≤ rankThreeGamma 1 3 (T : Subgroup K) ⊔
        sSup {V : Subgroup K | IsPGroup 2 V ∧ u ∈ normalizer (V : Set K)}

@[expose] def U3SylowData : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsRankThreeU3 K → ∀ (T : Sylow 3 K),
    Nat.card (T : Subgroup K) = 3 ^ 3 ∧ (∀ t ∈ (T : Subgroup K), t ^ 3 = 1) ∧
    ¬ IsMulCommutative (T : Subgroup K) ∧
    (∃ E : Subgroup K, E ≤ T ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2) ∧
    centralizer ((T : Subgroup K) : Set K) ≤ T ∧
    ∀ Y : Subgroup K, normalizer ((T : Subgroup K) : Set K) ≤ Y →
      Y = normalizer ((T : Subgroup K) : Set K) ∨ Y = ⊤

@[expose] def U3BorelCore : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal →
    centralizer (K : Set X) = ⊥ → IsRankThreeU3 ↥K →
    ∀ T : Subgroup X, T ≤ K → IsSylowOf 3 T K →
      rankThreePrimeCore 3 (normalizer (T : Set X)) = ⊥

@[expose] def U3AutData : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsRankThreeU3 K → ∀ S : Subgroup (MulAut K), IsPGroup 3 S →
    Nat.card S ∣ 3 ^ 3

end CFSG.LocalAnalysis.RankThreeTheoremC
