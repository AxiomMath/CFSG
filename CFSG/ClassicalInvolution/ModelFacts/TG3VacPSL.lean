module

public import CFSG.ClassicalInvolution.ModelFacts.TG3Common
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofPSL
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

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD.Exotic
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

section Pure

variable {n : ℕ}

theorem eq_of_central_ratio_longRoot (hn : 2 ≤ n) (hn4 : n ≠ 4) {L₁ L₂ : Subgroup SL(n, 𝔽₃)}
    {i₁ i₂ : SL(n, 𝔽₃)} (h₁ : IsLongRootSL2 hn L₁ i₁) (h₂ : IsLongRootSL2 hn L₂ i₂)
    (hc : i₂ * i₁⁻¹ ∈ Subgroup.center SL(n, 𝔽₃)) : L₁ = L₂ := by
  classical
  let _ : Fintype 𝔽₃ := Fintype.ofFinite _
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_three
  obtain ⟨r, hr, hscal⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow (by simp; omega)] at hr
    exact zero_ne_one hr
  have hr2 : r * r = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one r hr0
    have hcard : Fintype.card 𝔽₃ = 3 := by
      rw [← Nat.card_eq_fintype_card]
      exact natCard_galoisField_three
    rw [hcard] at h
    simpa [pow_two] using h
  have hi : (i₂ : Matrix (Fin n) (Fin n) 𝔽₃) =
      Matrix.scalar (Fin n) r * (i₁ : Matrix (Fin n) (Fin n) 𝔽₃) := by
    have h1 : i₂ = (i₂ * i₁⁻¹) * i₁ := by group
    have h3 := congrArg (fun A : SL(n, 𝔽₃) => (A : Matrix (Fin n) (Fin n) 𝔽₃)) h1
    rw [Matrix.SpecialLinearGroup.coe_mul (i₂ * i₁⁻¹) i₁, ← hscal] at h3
    exact h3
  rcases mul_self_eq_one_iff.mp hr2 with rfl | rfl
  · have : i₂ = i₁ := Subtype.ext (by simpa using hi)
    rw [h₁.eq_longRootGroup h2, h₂.eq_longRootGroup h2, this]
  · exfalso
    have hmin : minusSpace i₂ = fixSpace i₁ := by
      ext v
      rw [mem_minusSpace, mem_fixSpace, hi, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul,
        Matrix.smul_mulVec]
      simp
    have h1d := h₁.finrank_minusSpace h2
    have h2d := h₂.finrank_minusSpace h2
    have := Submodule.finrank_add_eq_of_isCompl (h₁.isCompl h2)
    rw [h1d, ← hmin, h2d, Module.finrank_fin_fun] at this
    omega

end Pure

section Model


theorem compGen3Twin_psl {k : ℕ} (hadm : StatedLieAdmissible .PSL k 3 1) (hk : k ≠ 4) :
    CompGen3Twin (compModel 3 1 .PSL k) := by
  have hk2 : 2 ≤ k := hadm.2.2.1
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hodd := odd_natCard_galoisField_three
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_three
  have hfin : Finite (compModel 3 1 .PSL (m + 1)).G :=
    finite_modelUniv (t := .PSL) hp2 Nat.prime_three trivial hadm
  have hL := fundamentalSubgroups_psl_eq (p := 3) (f := 1) (m := m) (by omega)
  intro X _ _ ψ hker R₁ hR₁ R₂ hR₂ h24₁ h24₂ hne hcomm z hz₁ hz₂ A hA hAle hzA
  exfalso
  obtain ⟨e₁⟩ := nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSL) trivial hadm
    (by decide) (by decide) hR₁
  obtain ⟨e₂⟩ := nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSL) trivial hadm
    (by decide) (by decide) hR₂
  have hcen := hker (twin_ratio_mem_ker ψ e₁ e₂ h24₁ h24₂ hz₁ hz₂)
  have hR₁' : R₁ ∈ longRootSet (K := 𝔽₃) (by omega : 2 ≤ m + 1) := by rw [← hL]; exact hR₁
  have hR₂' : R₂ ∈ longRootSet (K := 𝔽₃) (by omega : 2 ≤ m + 1) := by rw [← hL]; exact hR₂
  obtain ⟨i₁, hi₁⟩ := hR₁'
  obtain ⟨i₂, hi₂⟩ := hR₂'
  have hi₁e : i₁ = sl2Inv e₁ :=
    eq_sl2Inv_of_orderOf_eq_two hodd e₁ hi₁.mem ((hi₁.isClassicalSL2 h2).orderOf_eq_two)
  have hi₂e : i₂ = sl2Inv e₂ :=
    eq_sl2Inv_of_orderOf_eq_two hodd e₂ hi₂.mem ((hi₂.isClassicalSL2 h2).orderOf_eq_two)
  have hRR : R₁ = R₂ :=
    eq_of_central_ratio_longRoot (by omega) hk hi₁ hi₂ (by rw [hi₁e, hi₂e]; exact hcen)
  exact hne (by rw [hRR])

end Model

end CFSG.ClassicalInvolution.ModelFacts.TG3
