module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Proving

open Matrix Polynomial

section Algebra

variable {F : Type*} [Field F]

theorem mat2_mul_self (Y : Matrix (Fin 2) (Fin 2) F) :
    Y * Y = Y.trace • Y - Y.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem det_smul_one_add_smul (a b : F) (Y : Matrix (Fin 2) (Fin 2) F) :
    (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • Y).det =
      a ^ 2 + a * b * Y.trace + b ^ 2 * Y.det := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two]
  ring

theorem comm_eq_smul_add {X Y : Matrix (Fin 2) (Fin 2) F}
    (hY : ¬ ∃ c : F, Y = c • (1 : Matrix (Fin 2) (Fin 2) F)) (h : X * Y = Y * X) :
    ∃ a b : F, X = a • (1 : Matrix (Fin 2) (Fin 2) F) + b • Y := by
  have e : ∀ i j : Fin 2, (X * Y) i j = (Y * X) i j := fun i j => by rw [h]
  have e01 := e 0 1
  have e10 := e 1 0
  have e00 := e 0 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e01 e10 e00
  have E1 : (X 0 0 - X 1 1) * Y 0 1 = X 0 1 * (Y 0 0 - Y 1 1) := by linear_combination e01
  have E2 : X 1 0 * (Y 0 0 - Y 1 1) = Y 1 0 * (X 0 0 - X 1 1) := by linear_combination e10
  have E3 : X 0 1 * Y 1 0 = Y 0 1 * X 1 0 := by linear_combination e00
  suffices hb : ∃ b : F, X 0 1 = b * Y 0 1 ∧ X 1 0 = b * Y 1 0 ∧
      X 0 0 - X 1 1 = b * (Y 0 0 - Y 1 1) by
    obtain ⟨b, hb01, hb10, hbd⟩ := hb
    refine ⟨X 0 0 - b * Y 0 0, b, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · exact hb01
    · exact hb10
    · linear_combination -hbd
  by_cases h01 : Y 0 1 = 0
  · by_cases h10 : Y 1 0 = 0
    · have hd : Y 0 0 - Y 1 1 ≠ 0 := by
        intro hd
        apply hY
        refine ⟨Y 0 0, ?_⟩
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h01, h10]
        linear_combination -hd
      have hx01 : X 0 1 = 0 := by
        rw [h01, mul_zero] at E1
        exact (mul_eq_zero.1 E1.symm).resolve_right hd
      have hx10 : X 1 0 = 0 := by
        rw [h10, zero_mul] at E2
        exact (mul_eq_zero.1 E2).resolve_right hd
      refine ⟨(X 0 0 - X 1 1) / (Y 0 0 - Y 1 1), ?_, ?_, ?_⟩
      · rw [hx01, h01]; ring
      · rw [hx10, h10]; ring
      · field_simp
    · refine ⟨X 1 0 / Y 1 0, ?_, ?_, ?_⟩
      · have : X 0 1 = 0 := by
          rw [h01, zero_mul] at E3
          exact (mul_eq_zero.1 E3).resolve_right h10
        rw [this, h01]; ring
      · field_simp
      · field_simp
        linear_combination -E2
  · refine ⟨X 0 1 / Y 0 1, ?_, ?_, ?_⟩
    · field_simp
    · field_simp
      linear_combination -E3
    · field_simp
      linear_combination E1

theorem trace_det_of_sq_scalar {D : Matrix (Fin 2) (Fin 2) F} {c : F}
    (hD : D * D = c • (1 : Matrix (Fin 2) (Fin 2) F))
    (hDs : ¬ ∃ e : F, D = e • (1 : Matrix (Fin 2) (Fin 2) F)) :
    D.trace = 0 ∧ D.det = -c := by
  have h := mat2_mul_self D
  rw [hD] at h
  have h' : D.trace • D = (c + D.det) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [add_smul, h]; abel
  have htr : D.trace = 0 := by
    by_contra ht
    apply hDs
    refine ⟨(c + D.det) / D.trace, ?_⟩
    have := congrArg (fun M => D.trace⁻¹ • M) h'
    simp only [smul_smul, inv_mul_cancel₀ ht, one_smul] at this
    exact this.trans (by rw [div_eq_inv_mul])
  refine ⟨htr, ?_⟩
  rw [htr, zero_smul] at h'
  have := congrFun (congrFun h' 0) 0
  simp at this
  linear_combination -this

theorem exists_sl2_comm_aff [Finite F] (h2 : (2 : F) ≠ 0) (hcard : 5 < Nat.card F)
    {D : Matrix (Fin 2) (Fin 2) F} {c : F} (_hc : c ≠ 0) (htr : D.trace = 0) (hdet : D.det = -c) :
    ∃ B : Matrix.SpecialLinearGroup (Fin 2) F, (B : Matrix (Fin 2) (Fin 2) F) * D = D * B ∧
      ∃ a b : F, a ≠ 0 ∧ b ≠ 0 ∧
        (B : Matrix (Fin 2) (Fin 2) F) = a • (1 : Matrix (Fin 2) (Fin 2) F) + b • D := by
  classical
  obtain ⟨t, ht⟩ : ∃ t : F, t * (c * t ^ 2 - 1) * (c * t ^ 2 + 1) ≠ 0 := by
    let P : F[X] := X * (C c * X ^ 2 - C 1) * (C c * X ^ 2 + C 1)
    have hP : P ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero X_ne_zero ?_) ?_
      · intro h; have := congrArg (eval 0) h; simp at this
      · intro h; have := congrArg (eval 0) h; simp at this
    have hdeg : P.natDegree < Nat.card F := by
      have : P.natDegree ≤ 5 := by
        simp only [P]; compute_degree
      omega
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨r, hr⟩ := P.exists_eval_ne_zero_of_natDegree_lt_card hP (by
      rw [Cardinal.mk_fintype, ← Nat.card_eq_fintype_card]
      exact_mod_cast hdeg)
    exact ⟨r, by simpa [P] using hr⟩
  have ht0 : t ≠ 0 := fun h => ht (by rw [h]; ring)
  have h1 : c * t ^ 2 - 1 ≠ 0 := fun h => ht (by rw [h]; ring)
  have h3 : c * t ^ 2 + 1 ≠ 0 := fun h => ht (by rw [h]; ring)
  have h1' : 1 - c * t ^ 2 ≠ 0 := fun h => h1 (by linear_combination -h)
  set a : F := (1 + c * t ^ 2) / (1 - c * t ^ 2) with ha
  set b : F := 2 * t / (1 - c * t ^ 2) with hb
  have ha0 : a ≠ 0 := div_ne_zero (by simpa [add_comm] using h3) h1'
  have hb0 : b ≠ 0 := div_ne_zero (mul_ne_zero h2 ht0) h1'
  have hdet1 : (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • D).det = 1 := by
    rw [det_smul_one_add_smul, htr, hdet, ha, hb]
    field_simp
    ring
  refine ⟨⟨a • (1 : Matrix (Fin 2) (Fin 2) F) + b • D, hdet1⟩, ?_, a, b, ha0, hb0, rfl⟩
  simp [add_mul, mul_add]

theorem not_sq_scalar {D : Matrix (Fin 2) (Fin 2) F} {c a b : F} (h2 : (2 : F) ≠ 0) (ha : a ≠ 0)
    (hb : b ≠ 0) (hD : D * D = c • (1 : Matrix (Fin 2) (Fin 2) F))
    (hDs : ¬ ∃ e : F, D = e • (1 : Matrix (Fin 2) (Fin 2) F)) :
    ¬ ∃ e : F, (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • D) *
        (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • D) = e • (1 : Matrix (Fin 2) (Fin 2) F) := by
  rintro ⟨e, he⟩
  apply hDs
  have hsq : (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • D) *
      (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • D) =
      (a ^ 2 + b ^ 2 * c) • (1 : Matrix (Fin 2) (Fin 2) F) + (2 * a * b) • D := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hD, smul_smul]
    module
  rw [hsq] at he
  have hab : 2 * a * b ≠ 0 := mul_ne_zero (mul_ne_zero h2 ha) hb
  refine ⟨(e - (a ^ 2 + b ^ 2 * c)) / (2 * a * b), ?_⟩
  have : (2 * a * b) • D = (e - (a ^ 2 + b ^ 2 * c)) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [sub_smul]; rw [← he]; abel
  have := congrArg (fun M => (2 * a * b)⁻¹ • M) this
  simp only [smul_smul, inv_mul_cancel₀ hab, one_smul] at this
  rw [this, div_eq_inv_mul]

end Algebra

end CFSG.HardMathSupport.Seitz.TrialityOdd.Proving
