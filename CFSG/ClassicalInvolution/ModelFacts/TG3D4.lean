module

public import CFSG.ClassicalInvolution.ModelFacts.TG3D4Tri
public import CFSG.ClassicalInvolution.ModelFacts.TG3Models

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts.TG3

open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Uniform CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

section Transport

variable {ι : Type} [Fintype ι] {Q : QuadraticForm 𝔽₃ (ι → 𝔽₃)}
  {𝓕 : Set (Subgroup (spinGroup Q))}

theorem compGen3Twin_of_ctx_aut [Finite (spinGroup Q)] (c : SpinCtx3 Q 𝓕)
    (haut : ∀ {c₀ : spinGroup Q}, c₀ ∈ Subgroup.center (spinGroup Q) → c₀ * c₀ = 1 →
      ∃ σ : spinGroup Q ≃* spinGroup Q, (∀ R ∈ 𝓕, R.map σ.toMonoidHom ∈ 𝓕) ∧
        spinAction Q (σ c₀) = 1) :
    CompGen3Twin (⟨spinGroup Q, 𝓕⟩ : Q3.CompData) := by
  intro X _ _ ψ hker R₁ hR₁ R₂ hR₂ h24₁ h24₂ hne hcomm z hz₁ hz₂ A hA hAle hzA
  have hodd := odd_natCard_galoisField_three
  obtain ⟨e₁⟩ := c.hsl2 R₁ hR₁
  obtain ⟨e₂⟩ := c.hsl2 R₂ hR₂
  have hcen := twin_ratio_mem_ker ψ e₁ e₂ h24₁ h24₂ hz₁ hz₂
  have hcen' : sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∈ Subgroup.center (spinGroup Q) := hker hcen
  have hsq₁ := sl2Inv_mul_self hodd e₁
  have hsq₂ := sl2Inv_mul_self hodd e₂
  have hinv : (sl2Inv e₁)⁻¹ = sl2Inv e₁ := inv_eq_of_mul_eq_one_right hsq₁
  have hcomm₁₂ : sl2Inv e₁ * sl2Inv e₂ = sl2Inv e₂ * sl2Inv e₁ := by
    have hc := Subgroup.mem_center_iff.mp hcen' (sl2Inv e₁)
    rw [hinv] at hc
    have h3 := congrArg (fun x => x * sl2Inv e₁) hc
    simp only [mul_assoc, hsq₁, mul_one] at h3
    exact h3
  have hc2 : (sl2Inv e₂ * (sl2Inv e₁)⁻¹) * (sl2Inv e₂ * (sl2Inv e₁)⁻¹) = 1 := by
    rw [hinv]
    calc sl2Inv e₂ * sl2Inv e₁ * (sl2Inv e₂ * sl2Inv e₁)
        = sl2Inv e₂ * (sl2Inv e₁ * sl2Inv e₂) * sl2Inv e₁ := by group
      _ = sl2Inv e₂ * (sl2Inv e₂ * sl2Inv e₁) * sl2Inv e₁ := by rw [hcomm₁₂]
      _ = (sl2Inv e₂ * sl2Inv e₂) * (sl2Inv e₁ * sl2Inv e₁) := by group
      _ = 1 := by rw [hsq₁, hsq₂, mul_one]
  obtain ⟨σ, hσ𝓕, hθσ⟩ := haut hcen' hc2
  set ψ' : spinGroup Q →* X := ψ.comp σ.symm.toMonoidHom with hψ'
  have hmap : ∀ R : Subgroup (spinGroup Q), (R.map σ.toMonoidHom).map ψ' = R.map ψ := by
    intro R
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [hψ']
  have hrange : ψ'.range = ψ.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨σ.symm x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨σ x, by simp [hψ']⟩
  have hker' : ψ'.ker ≤ Subgroup.center (spinGroup Q) := by
    intro s hs
    have h1 : σ.symm s ∈ ψ.ker := by
      rw [MonoidHom.mem_ker] at hs ⊢
      exact hs
    have h2 := Subgroup.mem_center_iff.mp (hker h1)
    have : s = σ (σ.symm s) := by simp
    rw [this]
    refine Subgroup.mem_center_iff.mpr fun y => ?_
    have := h2 (σ.symm y)
    simpa using congrArg σ this
  let e₁' : ↥(R₁.map σ.toMonoidHom) ≃* SL(2, 𝔽₃) := (σ.subgroupMap R₁).symm.trans e₁
  let e₂' : ↥(R₂.map σ.toMonoidHom) ≃* SL(2, 𝔽₃) := (σ.subgroupMap R₂).symm.trans e₂
  have hs₁ : sl2Inv e₁' = σ (sl2Inv e₁) := rfl
  have hs₂ : sl2Inv e₂' = σ (sl2Inv e₂) := rfl
  have hord : spinAction Q (sl2Inv e₁') = spinAction Q (sl2Inv e₂') := by
    have h1 : sl2Inv e₂ = (sl2Inv e₂ * (sl2Inv e₁)⁻¹) * sl2Inv e₁ := by group
    rw [hs₁, hs₂, h1, map_mul, map_mul, hθσ, one_mul]
  have key := twin_generation_orth_ord c ψ' hker' (hσ𝓕 R₁ hR₁) (hσ𝓕 R₂ hR₂) e₁' e₂' hord
    (by rw [hmap]; exact h24₁) (by rw [hmap, hmap]; exact hne)
    (by rw [hmap, hmap]; exact hcomm) (z := z) (by rw [hmap]; exact hz₁) hA
    (by rw [hmap, hmap]; exact hAle) hzA
  rw [hrange] at key
  exact key

end Transport

section D4


theorem compGen3Twin_pOmegaPlus_four (hadm : StatedLieAdmissible .POmegaPlus 4 3 1) :
    CompGen3Twin (compModel 3 1 .POmegaPlus 4) := by
  have hn3 : 3 ≤ 4 := by norm_num
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hM : modelUniv .POmegaPlus 4 3 1 Fact.out =
      ⟨spinGroup (quadPlus 4 (GaloisField 3 1)), plusDatum 4 (GaloisField 3 1) hn3⟩ :=
    (rfl : modelUniv .POmegaPlus 4 3 1 Fact.out =
      ModelFacts.modelUniv .POmegaPlus 4 3 1 Fact.out).trans (modelUniv_POmegaPlus hn3)
  have hsingle : FundamentalSingleClass .POmegaPlus (modelUniv .POmegaPlus 4 3 1 Fact.out).D :=
    fundamentalSingleClass .POmegaPlus 4 3 1 Fact.out trivial hadm (by decide) (by decide)
  have hG3 : ∀ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 3 1 Fact.out).D,
      Gen3 R := fun R hR =>
    gen3_of_mem_longestFundamental3 (t := .POmegaPlus) h3 trivial hadm (by decide) (by decide)
      (fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR)
  have hlong : ∀ k : Fin (modelUniv .POmegaPlus 4 3 1 Fact.out).D.rank,
      IsLongestRoot (modelUniv .POmegaPlus 4 3 1 Fact.out).D (Pi.single k 1) :=
    fun k => isLongestRoot_single .POmegaPlus 4 3 1 Fact.out trivial hadm k trivial
  have hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 3 1 Fact.out).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .POmegaPlus) trivial hadm
      (by decide) (by decide) hR
  have hfin : Finite (modelUniv .POmegaPlus 4 3 1 Fact.out).K :=
    finite_modelUniv (t := .POmegaPlus) hp2 Nat.prime_three trivial hadm
  show CompGen3Twin ⟨(modelUniv .POmegaPlus 4 3 1 Fact.out).K,
    fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 3 1 Fact.out).D⟩
  generalize modelUniv .POmegaPlus 4 3 1 Fact.out = M at hM hsingle hG3 hlong hsl2 hfin ⊢
  subst hM
  have : Finite (spinGroup (quadPlus 4 (GaloisField 3 1))) := hfin
  exact compGen3Twin_of_ctx_aut (spinCtx3_plus hn3 le_rfl hsingle hlong hG3 hsl2)
    (fun {c₀} hc hc2 => exists_aut_ordinary3 hadm hc hc2)

end D4

end CFSG.ClassicalInvolution.ModelFacts.TG3
