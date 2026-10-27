module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Tr2

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L2Ord

open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem cheb_of_psl_pow {M : Matrix.SpecialLinearGroup (Fin 2) F} {n : ℕ}
    (hne : (QuotientGroup.mk M : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ≠ 1)
    (h : (QuotientGroup.mk M : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ^ (n + 1) = 1) :
    cheb (M : Matrix (Fin 2) (Fin 2) F).trace (n + 1) = 0 := by
  have h1 : M ^ (n + 1) ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact h
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h1
  refine cheb_eq_zero_of_pow_scalar M.2 (not_scalar_of_ne_one hne) (s := r) ?_
  rw [← Matrix.SpecialLinearGroup.coe_pow, ← hr]
  simp [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]

theorem sq_of_psl_pow_three {M : Matrix.SpecialLinearGroup (Fin 2) F}
    (hne : (QuotientGroup.mk M : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ≠ 1)
    (h : (QuotientGroup.mk M : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ^ 3 = 1) :
    (M : Matrix (Fin 2) (Fin 2) F).trace ^ 2 - 1 = 0 := by
  have := cheb_of_psl_pow (n := 2) hne h
  simp [cheb] at this
  linear_combination this

theorem quartic_of_psl_pow_five {M : Matrix.SpecialLinearGroup (Fin 2) F}
    (hne : (QuotientGroup.mk M : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ≠ 1)
    (h : (QuotientGroup.mk M : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ^ 5 = 1) :
    (M : Matrix (Fin 2) (Fin 2) F).trace ^ 4 - 3 * (M : Matrix (Fin 2) (Fin 2) F).trace ^ 2 + 1 =
      0 := by
  have := cheb_of_psl_pow (n := 4) hne h
  simp [cheb] at this
  linear_combination this

theorem psl_pow_five_of_trace [CharP F 5] {M : Matrix.SpecialLinearGroup (Fin 2) F}
    (hM : (M : Matrix (Fin 2) (Fin 2) F).trace = 3) :
    (QuotientGroup.mk M : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ^ 5 = 1 := by
  have h5 : (5 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 5
  have hpow := pow_eq (M : Matrix (Fin 2) (Fin 2) F) (sq_eq _ M.2) 4
  rw [hM] at hpow
  have e1 : cheb (3 : F) 5 = 0 := by
    simp [cheb]
    linear_combination 11 * h5
  have e2 : cheb (3 : F) 4 = 1 := by
    simp [cheb]
    linear_combination 4 * h5
  rw [e1, e2, zero_smul, one_smul, zero_sub] at hpow
  have hpow' : (M : Matrix (Fin 2) (Fin 2) F) ^ 5 = -1 := hpow
  have hc : M ^ 5 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    refine Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨-1, by simp, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_pow, hpow']
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact hc

theorem trace_conj_SL (G M : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((G * M * G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace =
      (M : Matrix (Fin 2) (Fin 2) F).trace := by
  have h1 : ((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (G : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem ne_one_of_conj_trace {M G : Matrix.SpecialLinearGroup (Fin 2) F}
    (hα : (M : Matrix (Fin 2) (Fin 2) F).trace ^ 2 = 1)
    (hc : ((M⁻¹ * (G * M * G⁻¹) : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F).trace = 3) (h23 : (2 : F) ≠ 3) :
    (QuotientGroup.mk (M⁻¹ * (G * M * G⁻¹)) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ≠
      1 := by
  intro h
  rw [QuotientGroup.eq_one_iff] at h
  obtain ⟨c, -, hcM⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have hM1 : ((M⁻¹ * (G * M * G⁻¹) : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = c • 1 := by
    rw [← hcM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  have hX : G * M * G⁻¹ = M * (M⁻¹ * (G * M * G⁻¹)) := by group
  have hXm : ((G * M * G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      c • (M : Matrix (Fin 2) (Fin 2) F) := by
    rw [hX, Matrix.SpecialLinearGroup.coe_mul, hM1, Matrix.mul_smul, Matrix.mul_one]
  have htr : (M : Matrix (Fin 2) (Fin 2) F).trace =
      c * (M : Matrix (Fin 2) (Fin 2) F).trace := by
    have := trace_conj_SL G M
    rw [hXm, Matrix.trace_smul, smul_eq_mul] at this
    exact this.symm
  have hc3 : 2 * c = 3 := by
    rw [hM1] at hc
    simpa [Matrix.trace_fin_two, mul_comm] using hc
  by_cases hc1 : c = 1
  · rw [hc1] at hc3
    exact h23 (by linear_combination hc3)
  · have : (c - 1) * (M : Matrix (Fin 2) (Fin 2) F).trace = 0 := by linear_combination -htr
    rcases mul_eq_zero.mp this with h0 | h0
    · exact hc1 (sub_eq_zero.mp h0)
    · rw [h0] at hα
      norm_num at hα

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L2Ord
