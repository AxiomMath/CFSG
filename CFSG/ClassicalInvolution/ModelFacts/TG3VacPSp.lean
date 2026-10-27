module

public import CFSG.ClassicalInvolution.ModelFacts.TG3Common
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalSymplectic
public import CFSG.ClassicalInvolution.Asc77.AscE189Sp4
public import CFSG.ClassicalInvolution.Uniform.U5Model
public import CFSG.ClassicalInvolution.ModelFacts.CF3All
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral
public import CFSG.ClassicalInvolution.Q3.Q3CSBase
public import CFSG.ClassicalInvolution.Q3.Q3DThm5
public import CFSG.ClassicalInvolution.Q3.Q3TAxis
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap
public import CFSG.ClassicalInvolution.Uniform.U3Thm8
public import CFSG.ClassicalInvolution.Uniform.U5Alpha
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts.TG3

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic Module
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped MatrixGroups Matrix

local notation "𝔽₃" => GaloisField 3 1

section Pure

variable {K : Type} [Field K] {n : ℕ}

theorem isCompl_minusSpace_fixSpace (h2 : (2 : K) ≠ 0) {i : StatedSp n K} (hi : i * i = 1) :
    IsCompl (minusSpace i) (fixSpace i) := by
  have hmat : ∀ v, mat n K i *ᵥ (mat n K i *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← map_mul, hi, map_one, Matrix.one_mulVec]
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro v hv₁ hv₂
    rw [mem_minusSpace] at hv₁
    rw [mem_fixSpace] at hv₂
    have h1 : v = -v := by rw [← hv₁, hv₂]
    have h3 : (2 : K) • v = 0 := by
      rw [two_smul]
      nth_rewrite 1 [h1]
      exact neg_add_cancel v
    exact (smul_eq_zero.mp h3).resolve_left h2
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hu : (2 : K)⁻¹ • (v - mat n K i *ᵥ v) ∈ minusSpace i := by
      rw [mem_minusSpace, Matrix.mulVec_smul, Matrix.mulVec_sub, hmat, ← smul_neg, neg_sub]
    have hw : (2 : K)⁻¹ • (v + mat n K i *ᵥ v) ∈ fixSpace i := by
      rw [mem_fixSpace, Matrix.mulVec_smul, Matrix.mulVec_add, hmat, add_comm]
    have hv : v = (2 : K)⁻¹ • (v - mat n K i *ᵥ v) + (2 : K)⁻¹ • (v + mat n K i *ᵥ v) := by
      rw [← smul_add]
      have : v - mat n K i *ᵥ v + (v + mat n K i *ᵥ v) = (2 : K) • v := by module
      rw [this, smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [hv]
    exact Submodule.add_mem_sup hu hw

end Pure

section PureThree

variable {n : ℕ}

theorem eq_of_central_ratio_longRootSp (hn : 2 ≤ n) (hn2 : n ≠ 2) {L₁ L₂ : Subgroup (StatedSp n 𝔽₃)}
    {i₁ i₂ : StatedSp n 𝔽₃} (h₁ : IsLongRootSp2 L₁ i₁) (h₂ : IsLongRootSp2 L₂ i₂)
    (hc : i₂ * i₁⁻¹ ∈ Subgroup.center (StatedSp n 𝔽₃)) : L₁ = L₂ := by
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_three
  have hi₁ : i₁ * i₁ = 1 := by
    have := (h₁.isClassicalSL2 h2).orderOf_eq_two
    rw [← pow_two, ← this]
    exact pow_orderOf_eq_one i₁
  have hζ2 : (i₂ * i₁⁻¹) * (i₂ * i₁⁻¹) = 1 := mul_self_eq_one_of_mem_center (by omega) hc
  by_cases hζ1 : i₂ * i₁⁻¹ = 1
  · have : i₂ = i₁ := mul_inv_eq_one.mp hζ1
    rw [h₁.eq_longRootGroup h2, h₂.eq_longRootGroup h2, this]
  · exfalso
    have hneg := mulVec_eq_neg_of_mem_center (by omega) hc hζ1 hζ2
    have hi : i₂ = (i₂ * i₁⁻¹) * i₁ := by group
    have hmin : minusSpace i₂ = fixSpace i₁ := by
      ext v
      rw [mem_minusSpace, mem_fixSpace]
      have hmat : mat n 𝔽₃ i₂ = mat n 𝔽₃ (i₂ * i₁⁻¹) * mat n 𝔽₃ i₁ := by
        rw [← map_mul, ← hi]
      rw [hmat, ← Matrix.mulVec_mulVec, hneg]
      exact neg_inj
    have hd₁ : finrank 𝔽₃ (minusSpace i₁) = 2 :=
      (isHyperbolicPlane_iff.mp (h₁.isHyperbolicPlane h2)).1
    have hd₂ : finrank 𝔽₃ (minusSpace i₂) = 2 :=
      (isHyperbolicPlane_iff.mp (h₂.isHyperbolicPlane h2)).1
    have hcompl := isCompl_minusSpace_fixSpace h2 hi₁
    have := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [hd₁, ← hmin, hd₂, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
      Fintype.card_fin] at this
    omega

end PureThree

section Model


theorem compGen3Twin_psp {n : ℕ} (hadm : StatedLieAdmissible .PSp n 3 1) (hn2 : n ≠ 2) :
    CompGen3Twin (compModel 3 1 .PSp n) := by
  have hn : 2 ≤ n := hadm.2.2.1
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hodd := odd_natCard_galoisField_three
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_three
  have hfin : Finite (compModel 3 1 .PSp n).G :=
    finite_modelUniv (t := .PSp) hp2 Nat.prime_three trivial hadm
  intro X _ _ ψ hker R₁ hR₁ R₂ hR₂ h24₁ h24₂ hne hcomm z hz₁ hz₂ A hA hAle hzA
  exfalso
  obtain ⟨e₁⟩ := nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSp) trivial hadm
    (by decide) (by decide) hR₁
  obtain ⟨e₂⟩ := nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSp) trivial hadm
    (by decide) (by decide) hR₂
  have hcen := hker (twin_ratio_mem_ker ψ e₁ e₂ h24₁ h24₂ hz₁ hz₂)
  obtain ⟨i₁, hi₁⟩ := (fund_iff_isLongRootSp2 hadm h2 R₁).mp hR₁
  obtain ⟨i₂, hi₂⟩ := (fund_iff_isLongRootSp2 hadm h2 R₂).mp hR₂
  have hi₁e : i₁ = sl2Inv e₁ :=
    eq_sl2Inv_of_orderOf_eq_two hodd e₁ ((hi₁.isClassicalSL2 h2).mem)
      ((hi₁.isClassicalSL2 h2).orderOf_eq_two)
  have hi₂e : i₂ = sl2Inv e₂ :=
    eq_sl2Inv_of_orderOf_eq_two hodd e₂ ((hi₂.isClassicalSL2 h2).mem)
      ((hi₂.isClassicalSL2 h2).orderOf_eq_two)
  have hRR : R₁ = R₂ :=
    eq_of_central_ratio_longRootSp hn hn2 hi₁ hi₂ (by rw [hi₁e, hi₂e]; exact hcen)
  exact hne (by rw [hRR])

end Model

end CFSG.ClassicalInvolution.ModelFacts.TG3
