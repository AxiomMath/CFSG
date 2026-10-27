module

public import CFSG.LinearAlgebra.SL2CoprimeOrder

public section

namespace CFSG.LinearAlgebra

theorem mul_self_eq_one_of_mulVec_eq_self {K : Type*} [Field K] [CharP K 2]
    (A : Matrix (Fin 2) (Fin 2) K) (hA : A.det = 1) {v : Fin 2 → K} (hv : v ≠ 0)
    (hAv : Matrix.mulVec A v = v) : A * A = 1 := by
  have htr : A.trace = 0 := by
    have h1 : Matrix.mulVec (A * A) v = v := by
      rw [← Matrix.mulVec_mulVec, hAv, hAv]
    rw [mul_self_eq_trace_smul_sub_one A hA, Matrix.sub_mulVec, Matrix.smul_mulVec,
      hAv, Matrix.one_mulVec] at h1
    have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
    have h2 : A.trace • v = 0 := by
      rw [sub_eq_iff_eq_add.mp h1, ← two_smul K v, h2K, zero_smul]
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    have hcoord : A.trace * v i = 0 := by
      simpa using congrFun h2 i
    exact (mul_eq_zero.mp hcoord).resolve_right hi
  rw [mul_self_eq_trace_smul_sub_one A hA, htr, zero_smul, zero_sub]
  ext i j
  simp [CharTwo.neg_eq]

end CFSG.LinearAlgebra

end
