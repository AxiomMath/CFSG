module

public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC

variable {G : Type*} [Group G]

@[expose] def NoRankTwoThree (C : Subgroup G) : Prop :=
  ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ * c₂ = c₂ * c₁ → c₁ ^ 3 = 1 → c₂ ^ 3 = 1 → c₁ ≠ 1 → c₂ ≠ 1 →
    c₂ ≠ c₁ → c₂ ≠ c₁⁻¹ → False

@[expose] def CyclicMod (P H : Subgroup G) : Prop :=
  ∃ g ∈ P, ∀ γ ∈ P, ∃ k : ℕ, ∃ h ∈ H, γ = g ^ k * h

theorem NoRankTwoThree.mono {C D : Subgroup G} (hD : NoRankTwoThree D) (hCD : C ≤ D) :
    NoRankTwoThree C :=
  fun c₁ h₁ c₂ h₂ => hD c₁ (hCD h₁) c₂ (hCD h₂)

end CFSG.LocalAnalysis.RankThreeUC
