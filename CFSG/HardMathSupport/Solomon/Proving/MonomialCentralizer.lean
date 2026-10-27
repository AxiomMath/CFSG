module

public import CFSG.HardMathSupport.Solomon.Proving.SU32Carrier

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open Matrix

theorem diag_rel_of_entry_ne_zero {K : Type} [Field K] (d : Fin 3 → K) (μ : K)
    (M : Matrix (Fin 3) (Fin 3) K)
    (h : M * Matrix.diagonal d = μ • (Matrix.diagonal d * M)) (i j : Fin 3)
    (hij : M i j ≠ 0) :
    d j = μ * d i := by
  have e := congrFun (congrFun h i) j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul] at e
  have h2 : M i j * (d j - μ * d i) = 0 := by linear_combination e
  rcases mul_eq_zero.1 h2 with h0 | h0
  · exact absurd h0 hij
  · linear_combination h0

theorem exists_entry_ne_zero_of_det_ne_zero {K : Type} [Field K] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) (hM : M.det ≠ 0) (i : n) :
    ∃ j, M i j ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact hM (Matrix.det_eq_zero_of_row_eq_zero i hcon)

theorem eq_of_entry_ne_zero_of_diag_injective {K : Type} [Field K] (d : Fin 3 → K)
    (hd : Function.Injective d) (μ : K) (M : Matrix (Fin 3) (Fin 3) K)
    (h : M * Matrix.diagonal d = μ • (Matrix.diagonal d * M)) (i j j' : Fin 3)
    (hj : M i j ≠ 0) (hj' : M i j' ≠ 0) : j = j' := by
  apply hd
  rw [diag_rel_of_entry_ne_zero d μ M h i j hj, diag_rel_of_entry_ne_zero d μ M h i j' hj']

theorem exists_smul_mul_of_comm_mem_scalar {K : Type} [Field K] (g h : GL (Fin 3) K)
    (hc : g * h * g⁻¹ * h⁻¹ ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3)).range) :
    ∃ μ : K, (g : Matrix (Fin 3) (Fin 3) K) * (h : Matrix (Fin 3) (Fin 3) K) =
      μ • ((h : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K)) := by
  obtain ⟨u, hu⟩ := hc
  refine ⟨u.1, ?_⟩
  have key : g * h = Matrix.GeneralLinearGroup.scalar (Fin 3) u * (h * g) := by
    rw [hu]
    group
  have e := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) key
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at e
  rw [e, ← Matrix.smul_eq_diagonal_mul]

end CFSG.HardMathSupport.Solomon.Proving
