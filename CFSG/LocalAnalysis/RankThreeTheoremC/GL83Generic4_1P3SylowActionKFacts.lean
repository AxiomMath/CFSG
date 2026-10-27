module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

@[expose] def KFactA6SylowAction : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsRankThreeA6 K → ∀ T : Sylow 3 K,
    (∃ n ∈ normalizer ((T : Subgroup K) : Set K), ∀ t ∈ (T : Subgroup K), n * t * n⁻¹ = t⁻¹) ∧
    ∀ t ∈ (T : Subgroup K), t ≠ 1 →
      ∃ n ∈ normalizer ((T : Subgroup K) : Set K), n * t * n⁻¹ ∉ zpowers t

@[expose] def KFactU3SylowInversion : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsRankThreeU3 K → ∀ T : Sylow 3 K,
    ∃ n ∈ normalizer ((T : Subgroup K) : Set K),
      ∀ z ∈ (center ↥(T : Subgroup K)).map (T : Subgroup K).subtype, n * z * n⁻¹ = z⁻¹

end CFSG.LocalAnalysis.RankThreeTheoremC
