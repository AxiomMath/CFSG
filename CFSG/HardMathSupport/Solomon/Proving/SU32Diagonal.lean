module

public import CFSG.HardMathSupport.Solomon.Proving.SU32Carrier

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open Matrix CFSG.Open

theorem cube_eq_one_of_ne_zero {K : Type} [Field K] (h4 : ∀ x : K, x ^ 4 = x) {x : K}
    (hx : x ≠ 0) : x ^ 3 = 1 := by
  have h : x * (x ^ 3 - 1) = 0 := by linear_combination h4 x
  rcases mul_eq_zero.1 h with h0 | h0
  · exact absurd h0 hx
  · exact sub_eq_zero.1 h0

theorem eq_zero_or_one_or_quad_of_card_four {K : Type} [Field K] (h4 : ∀ x : K, x ^ 4 = x)
    (x : K) : x = 0 ∨ x = 1 ∨ x ^ 2 + x + 1 = 0 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · have h3 : x ^ 3 = 1 := cube_eq_one_of_ne_zero h4 hx
    have h : (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.1 h with h0 | h0
    · exact Or.inr (Or.inl (sub_eq_zero.1 h0))
    · exact Or.inr (Or.inr h0)

theorem sq_mul_self_eq_one_of_ne_zero {K : Type} [Field K] (h4 : ∀ x : K, x ^ 4 = x) {x : K}
    (hx : x ≠ 0) : x ^ 2 * x = 1 := by
  rw [← pow_succ]
  exact cube_eq_one_of_ne_zero h4 hx

theorem exists_diag_mem_StatedSU_three_two (K : Type) [Field K] [Finite K] (hK : Nat.card K = 4)
    (a b c : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (habc : a * b * c = 1) :
    ∃ A : GL (Fin 3) K, (A : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![a, b, c] ∧
      A ∈ StatedSU 3 2 K := by
  have h4 := pow_four_eq_self K hK
  have hu : IsUnit (Matrix.diagonal ![a, b, c] : Matrix (Fin 3) (Fin 3) K) := by
    refine Matrix.isUnit_diagonal.2 (Pi.isUnit_iff.2 fun i => ?_)
    fin_cases i <;> simp [isUnit_iff_ne_zero, ha, hb, hc]
  refine ⟨hu.unit, hu.unit_spec, ?_⟩
  rw [mem_StatedSU_three_two_iff K hK, hu.unit_spec]
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simpa using habc
  · have hA := sq_mul_self_eq_one_of_ne_zero h4 ha
    have hB := sq_mul_self_eq_one_of_ne_zero h4 hb
    have hC := sq_mul_self_eq_one_of_ne_zero h4 hc
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.diagonal, hA, hB, hC]

end CFSG.HardMathSupport.Solomon.Proving
