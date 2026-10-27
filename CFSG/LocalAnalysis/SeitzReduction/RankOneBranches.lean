module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamilies

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG.Blueprint

@[expose] def RankOneLinearExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L → ∀ f : ℕ, 3 ≤ f →
    LieModel L .PSL 2 2 f → (∀ S : Sylow 2 (Subgroup.centralizer (L : Set G)), Nat.card S = 2) →
      False

@[expose] def RankOneUnitaryExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L → ∀ f : ℕ, 2 ≤ f →
    LieModel L .PSU 3 2 f → (∀ S : Sylow 2 (Subgroup.centralizer (L : Set G)), Nat.card S = 2) →
      False

@[expose] def RankOneSuzukiExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L → ∀ f : ℕ,
    LieModel L .twistedB2 0 2 f →
      (∀ S : Sylow 2 (Subgroup.centralizer (L : Set G)), Nat.card S = 2) → False

@[expose] def RankOneKernel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L → SeitzRankOne L →
    ∀ S : Sylow 2 (Subgroup.centralizer (L : Set G)), Nat.card S = 2

theorem seitzRankOneExclusion_of_kernel (hker : RankOneKernel) (h₁ : RankOneLinearExclusion)
    (h₂ : RankOneUnitaryExclusion) (h₃ : RankOneSuzukiExclusion) : SeitzRankOneExclusion := by
  refine seitzRankOneExclusion_of_families ?_ ?_ ?_
  · rintro G _ _ L hset ⟨f, hf, hm⟩
    exact h₁ G L hset f hf hm (hker G L hset (Or.inl ⟨f, hf, hm⟩))
  · rintro G _ _ L hset ⟨f, hf, hm⟩
    exact h₂ G L hset f hf hm (hker G L hset (Or.inr (Or.inl ⟨f, hf, hm⟩)))
  · rintro G _ _ L hset ⟨f, hm⟩
    exact h₃ G L hset f hm (hker G L hset (Or.inr (Or.inr ⟨f, hm⟩)))

end CFSG.SeitzReduction.RankOne
