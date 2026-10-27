module

public import CFSG.LocalAnalysis.Mason73.Model43
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 Equiv Subgroup

variable {n : ℕ}

theorem j1T_mem_T2T (hn : 2 ≤ n) : j1T (n := n) (by omega) ∈ T2T hn := by
  refine ⟨?_, ?_⟩
  · rw [j1T, piT_el]
    exact Or.inr (Or.inl rfl)
  · rw [j1T, psiT_el hn]
    simp [hv]

theorem j2T_mem_T2T (hn : 2 ≤ n) : j2T (n := n) (by omega) ∈ T2T hn := by
  refine ⟨?_, ?_⟩
  · rw [j2T, piT_el]
    exact Or.inr (Or.inr (Or.inl rfl))
  · rw [j2T, psiT_el hn]
    simp only [hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero, mul_one, mul_zero, add_zero]
    exact two_mul_hh (by omega)

theorem Q1_le_T2T (hn : 2 ≤ n) : Q1 (n := n) (by omega) ≤ T2T hn := by
  rw [Q1, closure_le]
  rintro _ (rfl | rfl)
  · exact r1T_mem_T2T hn
  · exact j1T_mem_T2T hn

theorem Q2_le_T2T (hn : 2 ≤ n) : Q2 (n := n) (by omega) ≤ T2T hn := by
  rw [Q2, closure_le]
  rintro _ (rfl | rfl)
  · exact r2T_mem_T2T hn
  · exact j2T_mem_T2T hn

theorem x1T_eq_mul_pow (hn : 2 ≤ n) :
    x1T (n := n) (by omega) = r1T n ^ 2 ^ (n - 2) * r2T n ^ 2 ^ (n - 2) := by
  have h2 := two_mul_zL4 (n := n) hn
  rw [r1T, r2T, el_one_pow, el_one_pow, el_mul, x1T, el_eq_el_iff hn]
  refine ⟨by rw [mul_one], isConst_of_forall_eq (-zL4 n) fun i => ?_⟩
  fin_cases i <;>
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, OneMemClass.coe_one, pv_one, hv, v1, v2,
      nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, Matrix.cons_val, Nat.cast_one, Nat.cast_zero,
      mul_one, mul_zero, mul_neg, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    first
    | ring1
    | linear_combination h2

theorem uT_eq_mul (hn : 2 ≤ n) :
    uT (n := n) (by omega) = x1T (by omega) * j2T (by omega) := by
  have h2 := hh_add_hh (n := n) (by omega)
  rw [x1T, j2T, el_mul, uT, el_eq_el_iff hn]
  refine ⟨by rw [one_mul], isConst_of_forall_eq 0 fun i => ?_⟩
  fin_cases i <;>
    simp only [Pi.sub_apply, Pi.add_apply, OneMemClass.coe_one, pv_one, hv, Matrix.cons_val,
      Nat.cast_one, Nat.cast_zero, mul_one, mul_zero, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    first
    | ring1
    | linear_combination h2

theorem vT_eq_mul (hn : 2 ≤ n) :
    vT (n := n) (by omega) = x1T (by omega) * j1T (by omega) := by
  have h2 := hh_add_hh (n := n) (by omega)
  rw [x1T, j1T, el_mul, vT, el_eq_el_iff hn]
  refine ⟨by rw [one_mul], isConst_of_forall_eq 0 fun i => ?_⟩
  fin_cases i <;>
    simp only [Pi.sub_apply, Pi.add_apply, OneMemClass.coe_one, pv_one, hv, Matrix.cons_val,
      Nat.cast_one, Nat.cast_zero, mul_one, mul_zero, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    first
    | ring1
    | linear_combination h2

theorem T2T_eq_sup (hn : 3 ≤ n) :
    T2T (n := n) (by omega) = Q1 (by omega) ⊔ Q2 (by omega) := by
  refine le_antisymm ((T2T_le_closure hn).trans ((closure_le _).2 ?_))
    (sup_le (Q1_le_T2T (by omega)) (Q2_le_T2T (by omega)))
  have hr1 : r1T n ∈ Q1 (n := n) (by omega) ⊔ Q2 (by omega) :=
    mem_sup_left (subset_closure (by simp))
  have hr2 : r2T n ∈ Q1 (n := n) (by omega) ⊔ Q2 (by omega) :=
    mem_sup_right (subset_closure (by simp))
  have hj1 : j1T (n := n) (by omega) ∈ Q1 (n := n) (by omega) ⊔ Q2 (by omega) :=
    mem_sup_left (subset_closure (by simp))
  have hj2 : j2T (n := n) (by omega) ∈ Q1 (n := n) (by omega) ⊔ Q2 (by omega) :=
    mem_sup_right (subset_closure (by simp))
  have hx1 : x1T (n := n) (by omega) ∈ Q1 (n := n) (by omega) ⊔ Q2 (by omega) := by
    rw [x1T_eq_mul_pow (by omega)]
    exact mul_mem (pow_mem hr1 _) (pow_mem hr2 _)
  rintro _ (rfl | rfl | rfl | rfl)
  · rw [SetLike.mem_coe, uT_eq_mul (by omega)]
    exact mul_mem hx1 hj2
  · rw [SetLike.mem_coe, vT_eq_mul (by omega)]
    exact mul_mem hx1 hj1
  · exact hr1
  · exact hr2

end CFSG.LocalAnalysis.Mason73
