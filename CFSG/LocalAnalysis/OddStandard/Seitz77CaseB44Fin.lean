module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseBFinW
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.OddStandard.Seitz77.CaseBFin

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FieldFourCover CFSG.ComponentClassification.PSL3Four
  CFSG.OddStandard.Seitz77.L34
open scoped commutatorElement

section Generation

private theorem tr01_eq (c : F4) :
    SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c = unipU F4 c 0 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe, coe_unipU]

private theorem tr12_eq (c : F4) :
    SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c = unipU F4 0 c 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe, coe_unipU]

private theorem tr02_eq (c : F4) :
    SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c = unipU F4 0 0 c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe, coe_unipU]

private theorem weylS1_mul_tr01 (c : F4) :
    weylS1 * SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c =
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c * weylS1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_weylS1, SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_three]

private theorem weylS2_mul_tr12 (c : F4) :
    weylS2 * SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c =
      SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c * weylS2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_weylS2, SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_three]

theorem unipAll_sup_weyl_eq_top :
    unipAll F4 ⊔ Subgroup.zpowers weylS1 ⊔ Subgroup.zpowers weylS2 =
      (⊤ : Subgroup (SpecialLinearGroup (Fin 3) F4)) := by
  set H := unipAll F4 ⊔ Subgroup.zpowers weylS1 ⊔ Subgroup.zpowers weylS2 with hH
  have hU : unipAll F4 ≤ H := le_sup_left.trans le_sup_left
  have hs1 : weylS1 ∈ H :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hs2 : weylS2 ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hconj : ∀ {g x : SpecialLinearGroup (Fin 3) F4}, g ∈ H → x ∈ H → g * x * g⁻¹ ∈ H :=
    fun {g x} hg hx => mul_mem (mul_mem hg hx) (inv_mem hg)
  have comm : ∀ {a b : SpecialLinearGroup (Fin 3) F4}, a ∈ H → b ∈ H → ⁅a, b⁆ ∈ H :=
    fun {a b} ha hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have h01 : ∀ c : F4, SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c ∈ H :=
    fun c => by rw [tr01_eq]; exact hU ⟨c, 0, 0, rfl⟩
  have h12 : ∀ c : F4, SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c ∈ H :=
    fun c => by rw [tr12_eq]; exact hU ⟨0, c, 0, rfl⟩
  have h02 : ∀ c : F4, SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c ∈ H :=
    fun c => by rw [tr02_eq]; exact hU ⟨0, 0, c, rfl⟩
  have h10 : ∀ c : F4, SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c ∈ H :=
    fun c => by
      have e : SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c =
          weylS1 * SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c *
            weylS1⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq, ← weylS1_mul_tr01]
      rw [e]
      exact hconj hs1 (h01 c)
  have h21 : ∀ c : F4, SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c ∈ H :=
    fun c => by
      have e : SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c =
          weylS2 * SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c *
            weylS2⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq, ← weylS2_mul_tr12]
      rw [e]
      exact hconj hs2 (h12 c)
  have h20 : ∀ c : F4, SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c ∈ H :=
    fun c => by
      have := SpecialLinearGroup.commutatorElement_transvection
        (show (2 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 0 by decide)
        (show (2 : Fin 3) ≠ 0 by decide) c (1 : F4)
      rw [mul_one] at this
      rw [← this]
      exact comm (h21 c) (h10 1)
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 3) (K := F4),
    Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | exact h01 c
      | exact h02 c
      | exact h10 c
      | exact h12 c
      | exact h20 c
      | exact h21 c

end Generation

section Normalize

private theorem det_two {K : Type} [Field K] (B : SpecialLinearGroup (Fin 2) K) :
    B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
  have h := B.2
  rwa [Matrix.det_fin_two] at h

theorem leviOne_mul_unipU_exists_field {K : Type} [Field K] (B : SpecialLinearGroup (Fin 2) K)
    (a c : K) :
    ∃ a' c' : K, leviOne K B * unipU K a 0 c = unipU K a' 0 c' * leviOne K B := by
  have hdet := det_two B
  refine ⟨a * B 1 1 - c * B 1 0, c * B 0 0 - a * B 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_leviOne, coe_unipU, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first
      | linear_combination (-a) * hdet
      | linear_combination (-c) * hdet

theorem leviTwo_mul_unipU_exists_field {K : Type} [Field K] (B : SpecialLinearGroup (Fin 2) K)
    (b c : K) :
    ∃ b' c' : K, leviTwo K B * unipU K 0 b c = unipU K 0 b' c' * leviTwo K B := by
  refine ⟨B 1 0 * c + B 1 1 * b, B 0 0 * c + B 0 1 * b, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_leviTwo, coe_unipU, Matrix.mul_apply, Fin.sum_univ_three]

theorem leviOne_mul_unipU_exists (B : SpecialLinearGroup (Fin 2) F4) (a c : F4) :
    ∃ a' c' : F4, leviOne F4 B * unipU F4 a 0 c = unipU F4 a' 0 c' * leviOne F4 B :=
  leviOne_mul_unipU_exists_field B a c

theorem leviTwo_mul_unipU_exists (B : SpecialLinearGroup (Fin 2) F4) (b c : F4) :
    ∃ b' c' : F4, leviTwo F4 B * unipU F4 0 b c = unipU F4 0 b' c' * leviTwo F4 B :=
  leviTwo_mul_unipU_exists_field B b c

end Normalize

section Perfect

private theorem commutator_top_SL2_F4 : commutator (SpecialLinearGroup (Fin 2) F4) = ⊤ :=
  (CFSG.LinearGroups.special_linear_dimension_two_perfect
    (CFSG.LinearGroups.exists_finset_card_eq_four natCard_F4.ge)).commutator_eq_top

private theorem perfect_range_of_hom
    (f : SpecialLinearGroup (Fin 2) F4 →* SpecialLinearGroup (Fin 3) F4) :
    ⁅f.range, f.range⁆ = f.range := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
    commutator_top_SL2_F4]

theorem perfect_range_leviOne :
    ⁅(leviOne F4).range, (leviOne F4).range⁆ = (leviOne F4).range :=
  perfect_range_of_hom _

theorem perfect_range_leviTwo :
    ⁅(leviTwo F4).range, (leviTwo F4).range⁆ = (leviTwo F4).range :=
  perfect_range_of_hom _

end Perfect

end CFSG.OddStandard.Seitz77.CaseBFin
