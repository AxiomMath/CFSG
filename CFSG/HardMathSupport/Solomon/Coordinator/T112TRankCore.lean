module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Nat.Totient

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix

variable {F : Type} [Field F]

theorem trace_eq_zero_of_nonscalar (h3 : (3 : F) ≠ 0) {M : Matrix (Fin 3) (Fin 3) F}
    (hM3 : M * M * M = 1) (hdet : M.det = 1) (hns : ∀ c : F, M ≠ c • 1) : M.trace = 0 := by
  by_contra htr
  have hCH := Matrix.aeval_self_charpoly M
  have hdeg : M.charpoly.natDegree = 3 := by
    rw [Matrix.charpoly_natDegree_eq_dim]; simp
  have hc3 : M.charpoly.coeff 3 = 1 := by
    have := (Matrix.charpoly_monic M).leadingCoeff
    rwa [Polynomial.leadingCoeff, hdeg] at this
  have hc2 : M.charpoly.coeff 2 = - M.trace := by
    have := Matrix.trace_eq_neg_charpoly_coeff M
    simp only [Fintype.card_fin] at this
    linear_combination this
  have hc0 : M.charpoly.coeff 0 = -1 := by
    have := Matrix.det_eq_sign_charpoly_coeff M
    simp only [Fintype.card_fin] at this
    rw [hdet] at this
    linear_combination this
  rw [Polynomial.aeval_eq_sum_range, hdeg] at hCH
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hc3, hc2, hc0] at hCH
  set c := M.charpoly.coeff 1 with hc
  have hM3' : M ^ 3 = 1 := by rw [pow_succ, pow_two]; exact hM3
  have hCH' : c • M + (-M.trace) • (M * M) = 0 := by
    rw [pow_zero, pow_one, pow_two, hM3'] at hCH
    have hCH2 : -1 + c • M + -(M.trace • (M * M)) + 1 = 0 := by simpa using hCH
    rw [neg_smul]
    calc c • M + -(M.trace • (M * M)) = -1 + c • M + -(M.trace • (M * M)) + 1 := by abel
      _ = 0 := hCH2
  have h5 : M * (M * M) = 1 := by rw [← mul_assoc]; exact hM3
  have h6 : M * M * (M * M) = M := by
    calc M * M * (M * M) = (M * M * M) * M := by simp only [mul_assoc]
      _ = M := by rw [hM3, one_mul]
  have h7 := congrArg (fun X => X * (M * M)) hCH'
  simp only [add_mul, smul_mul_assoc, zero_mul] at h7
  rw [h5, h6] at h7
  rw [neg_smul] at h7
  have h8 : c • (1 : Matrix (Fin 3) (Fin 3) F) = M.trace • M := add_neg_eq_zero.1 h7
  apply hns (c / M.trace)
  calc M = M.trace⁻¹ • (M.trace • M) := by rw [smul_smul, inv_mul_cancel₀ htr, one_smul]
    _ = (c / M.trace) • (1 : Matrix (Fin 3) (Fin 3) F) := by
      rw [← h8, smul_smul, div_eq_inv_mul]

theorem commute_of_mem_span {n : Type} [Fintype n] [DecidableEq n] (S : Set (Matrix n n F))
    (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) {y z : Matrix n n F}
    (hy : y ∈ Submodule.span F S) (hz : z ∈ Submodule.span F S) : y * z = z * y := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact hS y hy z hz
    | zero => simp
    | add y y' _ _ h1 h2 => rw [add_mul, mul_add, h1, h2]
    | smul c y _ h1 => rw [smul_mul_assoc, mul_smul_comm, h1]
  | zero => simp
  | add z z' _ _ h1 h2 => rw [mul_add, add_mul, h1, h2]
  | smul c z _ h1 => rw [mul_smul_comm, smul_mul_assoc, h1]

theorem false_of_nine_commuting {v : Fin 9 → Matrix (Fin 3) (Fin 3) F}
    (hv : LinearIndependent F v) (hc : ∀ i j, v i * v j = v j * v i) : False := by
  have hcard : Fintype.card (Fin 9) = Module.finrank F (Matrix (Fin 3) (Fin 3) F) := by
    simp [Module.finrank_matrix]
  have htop := LinearIndependent.span_eq_top_of_card_eq_finrank' hv hcard
  have hmem : ∀ x : Matrix (Fin 3) (Fin 3) F, x ∈ Submodule.span F (Set.range v) := by
    intro x; rw [htop]; trivial
  have := commute_of_mem_span (Set.range v) (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hc i j) (hmem (Matrix.single 0 1 1)) (hmem (Matrix.single 1 0 1))
  have h00 := congrFun (congrFun this 0) 0
  simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_three] at h00

end CFSG.HardMathSupport.Solomon.Coordinator
