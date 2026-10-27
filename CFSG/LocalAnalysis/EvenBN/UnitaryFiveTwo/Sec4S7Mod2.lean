module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7Mod
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.ClassicalGroups.UnitaryFlag Matrix Certificates.U52Yamada
open scoped commutatorElement

theorem uSU_mul_vSU_pow_four : (uSU * vSU) ^ 4 = 1 := by
  apply ext_mat
  rw [mat_pow_gen, mat_one]
  simp only [mat_mul, mat_uSU, mat_vSU]
  decide +kernel

theorem X₃sub_le_A₂sub : X₃sub ≤ A₂sub := le_sup_right.trans le_sup_left

theorem A₁sub_conj_e₁e₂ {a : SU52} (ha : a ∈ A₁sub) :
    (e₁SU * e₂SU) * a * (e₁SU * e₂SU)⁻¹ ∈ A₁sub :=
  conj_mem_A₁sub_of_comm_z e₁e₂_comm_zSU ha

theorem barInvT_eq_of_det_one (A : Matrix (Fin 2) (Fin 2) F4) (hA : A.det = 1) :
    barInvT hF4 A = !![bar (A 1 1), bar (A 1 0); bar (A 0 1), bar (A 0 0)] := by
  have hb : bar (A 0 0) * bar (A 1 1) - bar (A 0 1) * bar (A 1 0) = 1 := by
    have h := congrArg bar hA
    rw [Matrix.det_fin_two, map_sub, map_mul, map_mul, map_one] at h
    exact h
  have hc2 : ∀ x : F4, x + x = 0 := by decide
  refine barInvT_eq ?_
  rw [hF4_bar]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination hb + hc2 (bar (A 0 1) * bar (A 1 0))
  · linear_combination hc2 (bar (A 0 0) * bar (A 1 0))
  · linear_combination hc2 (bar (A 0 1) * bar (A 1 1))
  · linear_combination hb + hc2 (bar (A 0 1) * bar (A 1 0))

theorem mat_levSU_det_one_block (A : Matrix (Fin 2) (Fin 2) F4) (hA : IsUnit A.det)
    (hdet : A.det = 1) :
    mat (levSU A hA) 0 0 = bar (A 1 1) ∧ mat (levSU A hA) 0 1 = bar (A 1 0) ∧
      mat (levSU A hA) 1 0 = bar (A 0 1) ∧ mat (levSU A hA) 1 1 = bar (A 0 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    rw [mat_levSU, hdet, map_one, div_one, CFSG.ClassicalGroups.UnitaryFlag.oddDiag,
      barInvT_eq_of_det_one A hdet]
    simp [yIdx, blk3, Matrix.fromBlocks]

theorem mat_levSLHom_block (V : Matrix.SpecialLinearGroup (Fin 2) F4) :
    mat (levSLHom V) 0 0 = bar ((V : Matrix (Fin 2) (Fin 2) F4) 1 1) ∧
      mat (levSLHom V) 0 1 = bar ((V : Matrix (Fin 2) (Fin 2) F4) 1 0) ∧
      mat (levSLHom V) 1 0 = bar ((V : Matrix (Fin 2) (Fin 2) F4) 0 1) ∧
      mat (levSLHom V) 1 1 = bar ((V : Matrix (Fin 2) (Fin 2) F4) 0 0) := by
  have hdet : (V : Matrix (Fin 2) (Fin 2) F4).det = 1 := Matrix.SpecialLinearGroup.det_coe V
  have hU : IsUnit (V : Matrix (Fin 2) (Fin 2) F4).det := by
    rw [hdet]
    exact isUnit_one
  have e : levSLHom V = levSU (V : Matrix (Fin 2) (Fin 2) F4) hU := rfl
  rw [e]
  exact mat_levSU_det_one_block _ hU hdet

theorem eq_zero_of_bar_eq_zero {x : F4} (h : bar x = 0) : x = 0 := by
  rw [← bar_bar x, h, map_zero]

theorem eq_one_of_bar_eq_one {x : F4} (h : bar x = 1) : x = 1 := by
  rw [← bar_bar x, h, map_one]

theorem A₂sub_inf_K₂sub : A₂sub ⊓ K₂sub = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgA, hgK⟩ := mem_inf.1 hg
  rw [K₂sub_eq_levSLHom_range] at hgK
  obtain ⟨V, rfl⟩ := hgK
  obtain ⟨hS, h10⟩ := mem_A₂sub.1 hgA
  obtain ⟨hup, hdiag⟩ := mem_Ssub.1 hS
  obtain ⟨e00, e01, e10, e11⟩ := mat_levSLHom_block V
  have h01 : bar ((V : Matrix (Fin 2) (Fin 2) F4) 1 0) = 0 := by
    rw [← e01]
    exact hup 0 1 (by decide)
  have h10' : bar ((V : Matrix (Fin 2) (Fin 2) F4) 0 1) = 0 := by
    rw [← e10]
    exact h10
  have h00 : bar ((V : Matrix (Fin 2) (Fin 2) F4) 1 1) = 1 := by
    rw [← e00]
    exact hdiag 0
  have h11 : bar ((V : Matrix (Fin 2) (Fin 2) F4) 0 0) = 1 := by
    rw [← e11]
    exact hdiag 1
  have hV : V = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [eq_zero_of_bar_eq_zero h01, eq_zero_of_bar_eq_zero h10',
        eq_one_of_bar_eq_one h00, eq_one_of_bar_eq_one h11]
  exact mem_bot.2 (by rw [hV, map_one])

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
