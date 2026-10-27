module

import CFSG.Dihedral.GorensteinWalter.PGL2SquareRange
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.QuasiDihedralFusion

open Matrix

universe u

section SL2

variable {F : Type u} [Field F]

@[expose] def sl2U : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; -1, 0], by simp [det_fin_two]⟩

@[expose] def sl2T : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 1; 0, 1], by simp [det_fin_two]⟩

theorem coe_sl2U : ((sl2U : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    !![0, 1; -1, 0] := rfl

theorem coe_sl2T : ((sl2T : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    !![1, 1; 0, 1] := rfl

theorem coe_sl2U_mul_sl2U :
    ((sl2U * sl2U : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![-1, 0; 0, -1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2U]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2_mem_center_iff {A : SpecialLinearGroup (Fin 2) F} :
    A ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) ↔ A = 1 ∨ A = sl2U * sl2U := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hA⟩
    rw [Fintype.card_fin, sq] at hr
    rcases mul_self_eq_one_iff.mp hr with rfl | rfl
    · left
      ext i j
      rw [← hA]
      simp
    · right
      ext i j
      rw [← hA, coe_sl2U_mul_sl2U]
      fin_cases i <;> fin_cases j <;> simp
  · rintro (rfl | rfl)
    · exact ⟨1, by simp, by simp⟩
    · refine ⟨-1, by simp, ?_⟩
      rw [coe_sl2U_mul_sl2U]
      ext i j
      fin_cases i <;> fin_cases j <;> simp

theorem sl2U_mul_sl2U_mem_center :
    (sl2U * sl2U : SpecialLinearGroup (Fin 2) F) ∈ Subgroup.center _ :=
  sl2_mem_center_iff.mpr (Or.inr rfl)

theorem sl2U_mul_sl2U_ne_one (hF : ringChar F ≠ 2) :
    (sl2U * sl2U : SpecialLinearGroup (Fin 2) F) ≠ 1 := by
  intro h
  have h00 := congrArg
    (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [coe_sl2U_mul_sl2U, Matrix.SpecialLinearGroup.coe_one] at h00
  simp only [of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one,
    one_apply_eq] at h00
  exact Ring.neg_one_ne_one_of_char_ne_two hF h00

theorem sl2U_not_mem_center :
    (sl2U : SpecialLinearGroup (Fin 2) F) ∉ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  intro h
  rcases sl2_mem_center_iff.mp h with h1 | h1
  · have h01 := congrArg
      (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h1
    simp [coe_sl2U] at h01
  · have h01 := congrArg
      (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h1
    simp [coe_sl2U] at h01

theorem coe_sl2T_mul_sl2U_mul_inv :
    ((sl2T * sl2U * sl2T⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![-1, 2; -1, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, coe_sl2T, coe_sl2U, adjugate_fin_two_of]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two]

theorem sl2_conj_not_mem_center :
    (sl2U⁻¹ * (sl2T * sl2U * sl2T⁻¹) : SpecialLinearGroup (Fin 2) F) ∉
      Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  intro h
  have h00 : ∀ X : SpecialLinearGroup (Fin 2) F, sl2T * sl2U * sl2T⁻¹ = X →
      (X : Matrix (Fin 2) (Fin 2) F) 0 0 = -1 := by
    rintro X rfl
    rw [coe_sl2T_mul_sl2U_mul_inv]
    simp
  rcases sl2_mem_center_iff.mp h with h1 | h1
  · have h2 := h00 sl2U (inv_mul_eq_one.mp h1).symm
    simp [coe_sl2U] at h2
  · have hX : sl2T * sl2U * sl2T⁻¹ = sl2U * (sl2U * sl2U) := inv_mul_eq_iff_eq_mul.mp h1
    have h2 := h00 _ hX
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2U_mul_sl2U, coe_sl2U] at h2
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h2

theorem sq_mem_range_toPGL (g : ProjGenLinGroup (Fin 2) F) :
    g ^ 2 ∈ (Matrix.SpecialLinearGroup.toPGL :
      SpecialLinearGroup (Fin 2) F →* ProjGenLinGroup (Fin 2) F).range := by
  obtain ⟨x, hx⟩ := CFSG.GorensteinWalter.pgl2_sq_mem_psl2Range g
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨s, hx⟩

end SL2

end CFSG.QuasiDihedralFusion
