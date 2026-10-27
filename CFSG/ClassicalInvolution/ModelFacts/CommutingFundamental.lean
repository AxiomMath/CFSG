module

public import CFSG.ClassicalInvolution.Generic.Induction
public import CFSG.ClassicalInvolution.Models.Transfer.Basic

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def CommutingFundamentalGeneration (p : ℕ) [Fact p.Prime] (t : StatedLieTag)
    (n e : ℕ) : Prop :=
  ∀ R₁ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
    ∀ R₂ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
    ∀ c₁ ∈ R₁, ∀ c₂ ∈ R₂, (∀ r ∈ R₁, c₁ * r = r * c₁) → (∀ r ∈ R₂, c₂ * r = r * c₂) →
      (∀ r ∈ R₁, c₂ * r = r * c₂) → (∀ r ∈ R₂, c₁ * r = r * c₁) →
      (⊤ : Subgroup (modelUniv t n p e Fact.out).K) ≤
        ⨆ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
          ⨆ (_ : R ≤ Subgroup.centralizer ({c₁} : Set (modelUniv t n p e Fact.out).K) ∨
              R ≤ Subgroup.centralizer ({c₂} : Set (modelUniv t n p e Fact.out).K) ∨
              R ≤ Subgroup.centralizer ({c₁ * c₂} : Set (modelUniv t n p e Fact.out).K)), R

@[expose] def CommutingFundamentalFacts (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (t : StatedLieTag) (n e : ℕ), IsFundTag t → StatedLieAdmissible t n p e →
    CommutingFundamentalGeneration p t n e

section Transfer

variable {K X : Type*} [Group K] [Group X]

theorem range_le_iSup_of_commutingPair (ψ : K →* X) (hker : ψ.ker ≤ Subgroup.center K)
    {𝒮 : Set (Subgroup K)} (hperf : ∀ R ∈ 𝒮, ⁅R, R⁆ = R)
    (hgen : ∀ R₁ ∈ 𝒮, ∀ R₂ ∈ 𝒮, ∀ c₁ ∈ R₁, ∀ c₂ ∈ R₂, (∀ r ∈ R₁, c₁ * r = r * c₁) →
      (∀ r ∈ R₂, c₂ * r = r * c₂) → (∀ r ∈ R₁, c₂ * r = r * c₂) →
      (∀ r ∈ R₂, c₁ * r = r * c₁) →
      (⊤ : Subgroup K) ≤ ⨆ R ∈ 𝒮, ⨆ (_ : R ≤ Subgroup.centralizer ({c₁} : Set K) ∨
        R ≤ Subgroup.centralizer ({c₂} : Set K) ∨ R ≤ Subgroup.centralizer ({c₁ * c₂} : Set K)), R)
    {R₁ R₂ : Subgroup K} (h₁ : R₁ ∈ 𝒮) (h₂ : R₂ ∈ 𝒮) {u₁ u₂ : X} (hu₁ : u₁ ∈ R₁.map ψ)
    (hu₂ : u₂ ∈ R₂.map ψ) (hu₁₁ : ∀ y ∈ R₁.map ψ, u₁ * y = y * u₁)
    (hu₂₂ : ∀ y ∈ R₂.map ψ, u₂ * y = y * u₂) (hu₂₁ : ∀ y ∈ R₁.map ψ, u₂ * y = y * u₂)
    (hu₁₂ : ∀ y ∈ R₂.map ψ, u₁ * y = y * u₁) :
    ψ.range ≤ ⨆ R ∈ 𝒮, ⨆ (_ : (∀ y ∈ R.map ψ, u₁ * y = y * u₁) ∨
      (∀ y ∈ R.map ψ, u₂ * y = y * u₂) ∨ (∀ y ∈ R.map ψ, (u₁ * u₂) * y = y * (u₁ * u₂))),
        R.map ψ := by
  obtain ⟨c₁, hc₁R, rfl⟩ := hu₁
  obtain ⟨c₂, hc₂R, rfl⟩ := hu₂
  have cent : ∀ {R : Subgroup K} {g : K}, ⁅R, R⁆ = R → (∀ y ∈ R.map ψ, ψ g * y = y * ψ g) →
      ∀ r ∈ R, g * r = r * g := by
    intro R g hR hg r hr
    have h := Models.Transfer.mem_centralizer_of_map (θ := ψ) hker hR (g := g)
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hg y hy).symm)
    exact (Subgroup.mem_centralizer_iff.mp h r hr).symm
  have key := hgen R₁ h₁ R₂ h₂ c₁ hc₁R c₂ hc₂R (cent (hperf R₁ h₁) hu₁₁)
    (cent (hperf R₂ h₂) hu₂₂) (cent (hperf R₁ h₁) hu₂₁) (cent (hperf R₂ h₂) hu₁₂)
  set T : Subgroup X := ⨆ R ∈ 𝒮, ⨆ (_ : (∀ y ∈ R.map ψ, ψ c₁ * y = y * ψ c₁) ∨
    (∀ y ∈ R.map ψ, ψ c₂ * y = y * ψ c₂) ∨
      (∀ y ∈ R.map ψ, (ψ c₁ * ψ c₂) * y = y * (ψ c₁ * ψ c₂))), R.map ψ with hT
  have hle : (⨆ R ∈ 𝒮, ⨆ (_ : R ≤ Subgroup.centralizer ({c₁} : Set K) ∨
      R ≤ Subgroup.centralizer ({c₂} : Set K) ∨ R ≤ Subgroup.centralizer ({c₁ * c₂} : Set K)), R) ≤
      T.comap ψ := by
    refine iSup₂_le fun R hR => iSup_le fun hP => ?_
    have hP' : (∀ y ∈ R.map ψ, ψ c₁ * y = y * ψ c₁) ∨ (∀ y ∈ R.map ψ, ψ c₂ * y = y * ψ c₂) ∨
        (∀ y ∈ R.map ψ, (ψ c₁ * ψ c₂) * y = y * (ψ c₁ * ψ c₂)) := by
      rcases hP with h | h | h
      · left
        rintro _ ⟨r, hr, rfl⟩
        simpa only [map_mul] using
          (congrArg ψ (Subgroup.mem_centralizer_singleton_iff.mp (h hr))).symm
      · right
        left
        rintro _ ⟨r, hr, rfl⟩
        simpa only [map_mul] using
          (congrArg ψ (Subgroup.mem_centralizer_singleton_iff.mp (h hr))).symm
      · right
        right
        rintro _ ⟨r, hr, rfl⟩
        simpa only [map_mul] using
          (congrArg ψ (Subgroup.mem_centralizer_singleton_iff.mp (h hr))).symm
    exact Subgroup.map_le_iff_le_comap.mp (le_iSup₂_of_le R hR (le_iSup_of_le hP' le_rfl))
  rintro _ ⟨k, rfl⟩
  exact hle (key (Subgroup.mem_top k))

end Transfer

end CFSG.ClassicalInvolution.ModelFacts
