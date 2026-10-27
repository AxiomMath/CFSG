module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.LocalAnalysis.ComponentInitial LinearFlag

@[expose] def SL3InvertCentre : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J V : Subgroup Y) (K : Type) [Field K] [Finite K]
    [CharP K 2] (ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K) (d : ℕ), (d = 1 ∨ d = 2) →
    J ≤ L → (∀ l : ↥L, (l : Y) ∈ J ↔ ψ l ∈ stabilizer (flagSpace 3 K d)) →
    V ≤ J → ⁅V, V⁆ = V → (∀ W : Subgroup Y, W ≤ J → ⁅W, W⁆ = W → W ≤ V) → 3 ∣ Nat.card V →
    ∀ ζ : Y, ζ ∈ L → ζ ∈ Subgroup.centralizer (L : Set Y) → ζ ^ 3 = 1 → ζ ≠ 1 →
    ∀ t : Y, t ∈ Subgroup.normalizer (L : Set Y) → t ∈ Subgroup.normalizer (J : Set Y) →
      t * ζ * t⁻¹ = ζ⁻¹ →
      ¬ ∃ N : Subgroup Y, N ≤ V ∧ (∀ v ∈ V, ∀ n ∈ N, v * n * v⁻¹ ∈ N) ∧
        Nat.Coprime 3 (Nat.card N) ∧ ∀ v ∈ V, v * t * v⁻¹ * t⁻¹ ∈ N

end CFSG.LocalAnalysis.RankThreeTheoremC
