module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcReduce

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.LieType.Universal CFSG.Assembly.LowTwoRank

variable {K : Type} [Group K]

theorem pairFrame_of_centralizer_toral {t : StatedLieTag} (D : UniversalRootDatum K)
    (𝒯 : Subgroup K) (θ : Fin D.rank → ℤ) (hθ : IsLongestRoot D θ)
    (hsingle : FundamentalSingleClass t D)
    (hbase : ∀ c : K, (∀ r ∈ stdRankOne D θ, c * r = r * c) →
      (∃ g z : K, z ∈ stdRankOne D θ ∧ (∀ r ∈ stdRankOne D θ, z * r = r * z) ∧
        c = g * z * g⁻¹) →
      ∃ x : K, (∀ z ∈ stdRankOne D θ, (∀ r ∈ stdRankOne D θ, z * r = r * z) →
        x * z * x⁻¹ ∈ 𝒯) ∧ x * c * x⁻¹ ∈ 𝒯) :
    PairFrame 𝒯 (fundamentalSubgroups t D) := by
  have hRθ : stdRankOne D θ ∈ fundamentalSubgroups t D :=
    ⟨1, θ, Or.inl hθ, (conjSub_one _).symm⟩
  have key : ∀ R ∈ fundamentalSubgroups t D, ∃ g : K, conjSub g (stdRankOne D θ) = R := fun R hR =>
    hsingle _ hRθ R hR |>.imp fun g hg => hg.symm
  have hcent : ∀ {R : Subgroup K} {g : K} {c : K}, conjSub g (stdRankOne D θ) = R → c ∈ R →
      (∀ r ∈ R, c * r = r * c) → g⁻¹ * c * g ∈ stdRankOne D θ ∧
        ∀ r ∈ stdRankOne D θ, (g⁻¹ * c * g) * r = r * (g⁻¹ * c * g) := by
    intro R g c hg hc hcc
    subst hg
    refine ⟨mem_conjSub_iff.1 hc, fun r hr => ?_⟩
    have h := hcc (g * r * g⁻¹) (conj_mem_conjSub hr)
    calc g⁻¹ * c * g * r = g⁻¹ * (c * (g * r * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * r * g⁻¹) * c) * g := by rw [h]
      _ = r * (g⁻¹ * c * g) := by group
  intro R₁ hR₁ R₂ hR₂ c₁ hc₁ c₂ hc₂ hz₁ hz₂ hx₂₁ _hx₁₂
  obtain ⟨g₁, hg₁⟩ := key R₁ hR₁
  obtain ⟨g₂, hg₂⟩ := key R₂ hR₂
  obtain ⟨hc₁Θ, hc₁c⟩ := hcent hg₁ hc₁ hz₁
  obtain ⟨hc₂Θ, hc₂c⟩ := hcent hg₂ hc₂ hz₂
  have hc₂' : ∀ r ∈ stdRankOne D θ, (g₁⁻¹ * c₂ * g₁) * r = r * (g₁⁻¹ * c₂ * g₁) := by
    intro r hr
    have h := hx₂₁ (g₁ * r * g₁⁻¹) (hg₁ ▸ conj_mem_conjSub hr)
    calc g₁⁻¹ * c₂ * g₁ * r = g₁⁻¹ * (c₂ * (g₁ * r * g₁⁻¹)) * g₁ := by group
      _ = g₁⁻¹ * ((g₁ * r * g₁⁻¹) * c₂) * g₁ := by rw [h]
      _ = r * (g₁⁻¹ * c₂ * g₁) := by group
  have hconj : ∃ g z : K, z ∈ stdRankOne D θ ∧ (∀ r ∈ stdRankOne D θ, z * r = r * z) ∧
      g₁⁻¹ * c₂ * g₁ = g * z * g⁻¹ :=
    ⟨g₁⁻¹ * g₂, g₂⁻¹ * c₂ * g₂, hc₂Θ, hc₂c, by group⟩
  obtain ⟨x, hxz, hx𝒯⟩ := hbase _ hc₂' hconj
  refine ⟨g₁ * x⁻¹, ?_, ?_⟩
  · have : (g₁ * x⁻¹)⁻¹ * c₁ * (g₁ * x⁻¹) = x * (g₁⁻¹ * c₁ * g₁) * x⁻¹ := by group
    rw [this]
    exact hxz _ hc₁Θ hc₁c
  · have : (g₁ * x⁻¹)⁻¹ * c₂ * (g₁ * x⁻¹) = x * (g₁⁻¹ * c₂ * g₁) * x⁻¹ := by group
    rw [this]
    exact hx𝒯

end CFSG.ClassicalInvolution.ModelFacts
