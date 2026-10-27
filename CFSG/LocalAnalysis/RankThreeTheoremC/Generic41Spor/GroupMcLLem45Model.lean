module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.Native.HSMcLSmallData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open Subgroup CFSG.AGLEmbeddingD2 CFSG.RankThree.Native

@[expose] def McLLem45Model : Prop :=
  ∃ (R₀ : Subgroup ↥mcl275P) (u₀ w₀ : ↥mcl275P),
    Nat.card R₀ = 5 ^ 3 ∧ u₀ ∈ R₀ ∧ u₀ ^ 5 = 1 ∧ (∃ s ∈ R₀, s * u₀ ≠ u₀ * s) ∧
    w₀ * w₀ = 1 ∧ u₀ * w₀ * u₀⁻¹ ≠ w₀ ∧
    (∀ i j : ℕ, (u₀ ^ i * w₀ * (u₀ ^ i)⁻¹) * (u₀ ^ j * w₀ * (u₀ ^ j)⁻¹) =
      (u₀ ^ j * w₀ * (u₀ ^ j)⁻¹) * (u₀ ^ i * w₀ * (u₀ ^ i)⁻¹)) ∧
    (∀ x ∈ R₀, (∃ s ∈ R₀, s * x ≠ x * s) →
      ∃ n ∈ normalizer (R₀ : Set ↥mcl275P), n * u₀ * n⁻¹ = x)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
