module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bRows

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def CFProp21A10 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52 H), h.Row515 →
    Nat.card (↥h.T ⧸ h.B.subgroupOf h.T) = 4 ∧ ∀ t ∈ h.T, t ^ 2 ∈ h.B

@[expose] def CFA10Local : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52 H), h.Row515 →
    Nat.card ↥(h.T ⊓ h.K) = 4 ∧ (∀ u ∈ h.T ⊓ h.K, u ^ 2 = 1) ∧
    (∃ N₀ : Subgroup H, N₀ ≤ h.K ∧ N₀ ≤ normalizer (h.T : Set H) ∧
      N₀ ≤ centralizer (h.B : Set H) ∧
      (∀ u ∈ h.T ⊓ h.K, ∀ v ∈ h.T ⊓ h.K, u ≠ 1 → v ≠ 1 → ∃ n ∈ N₀, n * u * n⁻¹ = v) ∧
      ∃ n ∈ N₀, (∃ k : ℕ, n ^ 2 ^ k = 1) ∧ ∃ u ∈ h.T ⊓ h.K, n * u * n⁻¹ ≠ u) ∧
    (h.a ∈ h.T ⊓ h.K → ∃ g ∈ h.K, g⁻¹ * h.a * g ∈ h.D)

@[expose] def CFA10NoOuter : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52 H), h.Row515 →
    h.W ≤ h.K ⊔ coreActionKernel h.K

end CFSG.ComponentClassification.GSThmB
