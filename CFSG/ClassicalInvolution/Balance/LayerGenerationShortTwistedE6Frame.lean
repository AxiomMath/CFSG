module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortTwistedE6
public import CFSG.ClassicalInvolution.ModelFacts.TwistedE6PairCore

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.ClassicalInvolution.ModelFacts.LeviE6

section Reduction

variable {K : Type} [Group K]

theorem pairFrame_of_hbase {t : StatedLieTag} (D : UniversalRootDatum K) (𝒯 : Subgroup K)
    (θ : Fin D.rank → ℤ) (hθ : IsLongestRoot D θ) (hsingle : FundamentalSingleClass t D)
    (hbase : ∀ c₁ c₂ : K, c₁ ∈ D.rootGroup θ ⊔ D.rootGroup (-θ) →
      (∀ r ∈ D.rootGroup θ ⊔ D.rootGroup (-θ), c₁ * r = r * c₁) →
      (∀ r ∈ D.rootGroup θ ⊔ D.rootGroup (-θ), c₂ * r = r * c₂) →
      (∃ g z : K, z ∈ D.rootGroup θ ⊔ D.rootGroup (-θ) ∧
        (∀ r ∈ D.rootGroup θ ⊔ D.rootGroup (-θ), z * r = r * z) ∧ c₂ = g * z * g⁻¹) →
      ∃ x : K, x * c₁ * x⁻¹ ∈ 𝒯 ∧ x * c₂ * x⁻¹ ∈ 𝒯) :
    PairFrame 𝒯 (fundamentalSubgroups t D) := by
  have hRθ : D.rootGroup θ ⊔ D.rootGroup (-θ) ∈ fundamentalSubgroups t D :=
    ⟨1, θ, Or.inl hθ, (conjSub_one _).symm⟩
  have key : ∀ R ∈ fundamentalSubgroups t D, ∃ g : K,
      conjSub g (D.rootGroup θ ⊔ D.rootGroup (-θ)) = R := fun R hR =>
    hsingle _ hRθ R hR |>.imp fun g hg => hg.symm
  have hcent : ∀ {R : Subgroup K} {g c : K},
      conjSub g (D.rootGroup θ ⊔ D.rootGroup (-θ)) = R → c ∈ R → (∀ r ∈ R, c * r = r * c) →
      g⁻¹ * c * g ∈ D.rootGroup θ ⊔ D.rootGroup (-θ) ∧
        ∀ r ∈ D.rootGroup θ ⊔ D.rootGroup (-θ), (g⁻¹ * c * g) * r = r * (g⁻¹ * c * g) := by
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
  have hc₂' : ∀ r ∈ D.rootGroup θ ⊔ D.rootGroup (-θ),
      (g₁⁻¹ * c₂ * g₁) * r = r * (g₁⁻¹ * c₂ * g₁) := by
    intro r hr
    have h := hx₂₁ (g₁ * r * g₁⁻¹) (hg₁ ▸ conj_mem_conjSub hr)
    calc g₁⁻¹ * c₂ * g₁ * r = g₁⁻¹ * (c₂ * (g₁ * r * g₁⁻¹)) * g₁ := by group
      _ = g₁⁻¹ * ((g₁ * r * g₁⁻¹) * c₂) * g₁ := by rw [h]
      _ = r * (g₁⁻¹ * c₂ * g₁) := by group
  have hconj : ∃ g z : K, z ∈ D.rootGroup θ ⊔ D.rootGroup (-θ) ∧
      (∀ r ∈ D.rootGroup θ ⊔ D.rootGroup (-θ), z * r = r * z) ∧
      g₁⁻¹ * c₂ * g₁ = g * z * g⁻¹ :=
    ⟨g₁⁻¹ * g₂, g₂⁻¹ * c₂ * g₂, hc₂Θ, hc₂c, by group⟩
  obtain ⟨x, hx₁, hx₂⟩ := hbase _ _ hc₁Θ hc₁c hc₂' hconj
  refine ⟨g₁ * x⁻¹, ?_, ?_⟩
  · have : (g₁ * x⁻¹)⁻¹ * c₁ * (g₁ * x⁻¹) = x * (g₁⁻¹ * c₁ * g₁) * x⁻¹ := by group
    rw [this]
    exact hx₁
  · have : (g₁ * x⁻¹)⁻¹ * c₂ * (g₁ * x⁻¹) = x * (g₁⁻¹ * c₂ * g₁) * x⁻¹ := by group
    rw [this]
    exact hx₂

end Reduction

section Final

variable {p n e : ℕ} [Fact p.Prime]

theorem twistedE6_pairFrame (hadm : StatedLieAdmissible .twistedE6 n p e) (hp2 : p ≠ 2) :
    TwistedE6PairFrame p n e := by
  have hsingle : FundamentalSingleClass .twistedE6
      (modelUniv .twistedE6 n p e Fact.out).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .twistedE6 n p e Fact.out trivial
      hadm (by decide) (by decide)
  have hθ : IsLongestRoot (modelUniv .twistedE6 n p e Fact.out).D (proj thetaE6) :=
    CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_twistedDatum_proj (frobQ p e)
      isRoot_thetaE6 rho_thetaE6
  exact pairFrame_of_hbase (modelUniv .twistedE6 n p e Fact.out).D (twistedE6SignGroup n p e)
    (proj thetaE6) hθ hsingle fun c₁ c₂ hc₁ hc₁c hc₂c hconj =>
      twistedE6_hbase hp2 hadm.2.1 hc₁ hc₁c hc₂c hconj

theorem layerGenerationPairAt_twistedE6_final (hadm : StatedLieAdmissible .twistedE6 n p e)
    (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e) : LayerGenerationPairAt .twistedE6 n p e Fact.out :=
  layerGenerationPairAt_twistedE6 hadm hp2 h5 (twistedE6_pairFrame hadm hp2)

end Final

end CFSG.ClassicalInvolution.Balance.Bootstrap
