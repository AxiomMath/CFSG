module

public import CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320

open Matrix Matrix.SpecialLinearGroup CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine
open scoped commutatorElement

variable {k : Type} [Field k]

@[expose] def x01 (c : k) : SpecialLinearGroup (Fin 3) k := transvection (show (0 : Fin 3) ≠ 1 by decide) c

@[expose] def x12 (c : k) : SpecialLinearGroup (Fin 3) k := transvection (show (1 : Fin 3) ≠ 2 by decide) c

@[expose] def x20 (c : k) : SpecialLinearGroup (Fin 3) k := transvection (show (2 : Fin 3) ≠ 0 by decide) c

theorem coe_x01 (c : k) : ((x01 c : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
    !![1, c, 0; 0, 1, 0; 0, 0, 1] := by
  rw [x01, transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem coe_x12 (c : k) : ((x12 c : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
    !![1, 0, 0; 0, 1, c; 0, 0, 1] := by
  rw [x12, transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem coe_x20 (c : k) : ((x20 c : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
    !![1, 0, 0; 0, 1, 0; c, 0, 1] := by
  rw [x20, transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem comm_mem {G : Type*} [Group G] (H : Subgroup G) {a b : G} (ha : a ∈ H) (hb : b ∈ H) :
    ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem eq_top_of_transvections (H : Subgroup (SpecialLinearGroup (Fin 3) k))
    (h01 : ∀ c, x01 c ∈ H) (h12 : ∀ c, x12 c ∈ H) (h20 : ∀ c, x20 c ∈ H) : H = ⊤ := by
  have hall : ∀ (i j : Fin 3) (hij : i ≠ j) (c : k), transvection hij c ∈ H := by
    intro i j hij c
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h01 c
    · have := commutatorElement_transvection (show (0 : Fin 3) ≠ 1 by decide)
        (show (1 : Fin 3) ≠ 2 by decide) (show (0 : Fin 3) ≠ 2 by decide) c 1
      rw [mul_one] at this
      rw [← this]
      exact comm_mem H (h01 c) (h12 1)
    · have := commutatorElement_transvection (show (1 : Fin 3) ≠ 2 by decide)
        (show (2 : Fin 3) ≠ 0 by decide) (show (1 : Fin 3) ≠ 0 by decide) c 1
      rw [mul_one] at this
      rw [← this]
      exact comm_mem H (h12 c) (h20 1)
    · exact absurd rfl hij
    · exact h12 c
    · exact h20 c
    · have := commutatorElement_transvection (show (2 : Fin 3) ≠ 0 by decide)
        (show (0 : Fin 3) ≠ 1 by decide) (show (2 : Fin 3) ≠ 1 by decide) c 1
      rw [mul_one] at this
      rw [← this]
      exact comm_mem H (h20 c) (h01 1)
    · exact absurd rfl hij
  rw [eq_top_iff, ← closure_range_toSpecialLinearGroup_eq_top_of_field (K := k) (ι := Fin 3),
    Subgroup.closure_le]
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  rw [TransvectionStruct.toSpecialLinearGroup_mk]
  exact hall i j hij c

theorem rSL_conj_x12 (c : k) : (rSL : SpecialLinearGroup (Fin 3) k) * x12 c * rSL⁻¹ = x20 c := by
  apply Subtype.ext
  rw [rSL_inv, coe_mul, coe_mul, coe_mul, coe_rSL, coe_x12, coe_x20]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem rSL_conj_x20 (c : k) : (rSL : SpecialLinearGroup (Fin 3) k) * x20 c * rSL⁻¹ = x01 c := by
  apply Subtype.ext
  rw [rSL_inv, coe_mul, coe_mul, coe_mul, coe_rSL, coe_x20, coe_x01]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem rSL_conj_x01 (c : k) : (rSL : SpecialLinearGroup (Fin 3) k) * x01 c * rSL⁻¹ = x12 c := by
  apply Subtype.ext
  rw [rSL_inv, coe_mul, coe_mul, coe_mul, coe_rSL, coe_x01, coe_x12]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem eq_top_of_x12 (H : Subgroup (SpecialLinearGroup (Fin 3) k))
    (hr : ∀ h ∈ H, (rSL : SpecialLinearGroup (Fin 3) k) * h * rSL⁻¹ ∈ H) (h12 : ∀ c, x12 c ∈ H) :
    H = ⊤ :=
  eq_top_of_transvections H (fun c => rSL_conj_x20 c ▸ hr _ (rSL_conj_x12 c ▸ hr _ (h12 c))) h12
    (fun c => rSL_conj_x12 c ▸ hr _ (h12 c))

theorem eq_top_of_x01 (H : Subgroup (SpecialLinearGroup (Fin 3) k))
    (hr : ∀ h ∈ H, (rSL : SpecialLinearGroup (Fin 3) k) * h * rSL⁻¹ ∈ H) (h01 : ∀ c, x01 c ∈ H) :
    H = ⊤ :=
  eq_top_of_x12 H hr (fun c => rSL_conj_x01 c ▸ hr _ (h01 c))

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320
