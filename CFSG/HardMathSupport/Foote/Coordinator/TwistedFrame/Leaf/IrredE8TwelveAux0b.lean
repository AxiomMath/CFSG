module

public import Mathlib.FieldTheory.IsAlgClosed.Basic

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrE8

open Polynomial

theorem poly_eq_zero_of_eval {L : Type} [Field L] [IsAlgClosed L] {N : ℕ} (hN : 2 ≤ N)
    (hNL : (N : L) = 0) {ε : L} (hε : ε ≠ 0) {P : L[X]} (hP : P.natDegree < N)
    (h : ∀ x : L, x ^ N = ε * x → P.eval x = 0) : P = 0 := by
  classical
  set f : L[X] := X ^ N - C ε * X with hf
  have hfdeg : f.natDegree = N := by
    have h1 : (C ε * X : L[X]).natDegree ≤ 1 := by
      calc (C ε * X : L[X]).natDegree ≤ (C ε : L[X]).natDegree + (X : L[X]).natDegree :=
            natDegree_mul_le
        _ ≤ 0 + 1 := by simp
        _ = 1 := by norm_num
    rw [hf, natDegree_sub_eq_left_of_natDegree_lt (by simpa using lt_of_le_of_lt h1 hN),
      natDegree_X_pow]
  have hder : derivative f = - C ε := by
    rw [hf]
    simp [derivative_X_pow, hNL]
  have hsep : f.Separable := by
    rw [Polynomial.Separable, hder]
    refine ⟨0, -C ε⁻¹, ?_⟩
    rw [zero_mul, zero_add, neg_mul_neg, ← C_mul, inv_mul_cancel₀ hε, C_1]
  have hcard := card_rootSet_eq_natDegree (K := L) hsep (IsAlgClosed.splits _)
  rw [hfdeg] at hcard
  refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P (f.rootSet L).toFinset ?_ ?_
  · intro x hx
    rw [Set.mem_toFinset, mem_rootSet] at hx
    obtain ⟨-, hx⟩ := hx
    apply h
    simp only [hf, map_sub, map_pow, aeval_X, map_mul, aeval_C, Algebra.algebraMap_self,
      RingHom.id_apply] at hx
    exact sub_eq_zero.1 hx
  · rw [Set.toFinset_card, hcard]
    exact hP


theorem sum_coeff_eq_zero {L : Type} [Field L] [IsAlgClosed L] {N : ℕ} (hN : 2 ≤ N)
    (hNL : (N : L) = 0) {ε : L} (hε : ε ≠ 0) {ι : Type} [Fintype ι] (c : ι → L) (e : ι → ℕ)
    (he : Function.Injective e) (hlt : ∀ i, e i < N)
    (h : ∀ x : L, x ^ N = ε * x → ∑ i, c i * x ^ e i = 0) : ∀ i, c i = 0 := by
  classical
  set P : L[X] := ∑ i, C (c i) * X ^ (e i) with hP
  have hdeg : P.natDegree < N := by
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := N - 1) fun i _ => ?_) (by omega)
    refine (natDegree_C_mul_X_pow_le (c i) (e i)).trans ?_
    have := hlt i
    omega
  have hz : P = 0 := poly_eq_zero_of_eval hN hNL hε hdeg fun x hx => by
    simp only [hP, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
    exact h x hx
  intro i
  have h1 : P.coeff (e i) = c i := by
    simp only [hP, finset_sum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have : e i ≠ e j := fun h' => hji (he h').symm
      simp [this]
    · intro h'
      exact absurd (Finset.mem_univ i) h'
  rw [← h1, hz, coeff_zero]

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrE8
