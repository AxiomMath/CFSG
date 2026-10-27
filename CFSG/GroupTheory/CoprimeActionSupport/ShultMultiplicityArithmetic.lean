module


public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.ShultMultiplicityArithmetic

theorem sum_eq_prime_sub_one {r N : ℕ} (hr : Nat.Prime r) (hr2 : r ≠ 2) (hN : 2 ≤ N)
    (a : Fin r → ℕ) (ha0 : a ⟨0, hr.pos⟩ = 0) (hsum : ∑ i, a i = N)
    (hsq : r * ∑ i, a i ^ 2 = N ^ 2 + r - 1) : N = r - 1 := by
  have core {r N : ℕ} (hr : Nat.Prime r) (hr2 : r ≠ 2) (hN : 2 ≤ N) (a : Fin r → ℕ)
      (ha0 : a ⟨0, hr.pos⟩ = 0) (hsum : ∑ i, a i = N)
      (hsq : r * ∑ i, a i ^ 2 = N ^ 2 + r - 1) :
      N = r - 1 ∧ ∑ i, a i ^ 2 = N := by
    have hr1 : 1 ≤ r := hr.pos
    set i0 : Fin r := ⟨0, hr.pos⟩ with hi0
    set S2 := ∑ i, a i ^ 2 with hS2

    have hCS : (∑ i ∈ Finset.univ.erase i0, a i) ^ 2 ≤
        (Finset.univ.erase i0).card * ∑ i ∈ Finset.univ.erase i0, a i ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have hc : (Finset.univ.erase i0).card = r - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
    have e1 : ∑ i ∈ Finset.univ.erase i0, a i = N := by
      rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i0), ha0, zero_add]
    have e2 : ∑ i ∈ Finset.univ.erase i0, a i ^ 2 = S2 := by
      rw [hS2, ← Finset.add_sum_erase _ _ (Finset.mem_univ i0), ha0]; simp
    rw [e1, e2, hc] at hCS
    have hge : N ≤ S2 := by
      rw [← hsum]
      exact Finset.sum_le_sum fun i _ => by nlinarith [Nat.zero_le (a i), Nat.le_self_pow (two_ne_zero) (a i)]

    obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hc hCS ⊢
    have hsq' : (k + 1) * S2 = N ^ 2 + k := by
      have : N ^ 2 + (k + 1) - 1 = N ^ 2 + k := by omega
      rw [this] at hsq; exact hsq
    have hle : S2 ≤ k := by nlinarith
    have hNk : N ≤ k := le_trans hge hle
    have hNk' : N = k := by
      by_contra hne
      have hlt : N + 1 ≤ k := by omega

      have : (k + 1) * N ≤ N ^ 2 + k := by rw [← hsq']; exact Nat.mul_le_mul_left _ hge
      nlinarith
    refine ⟨hNk', le_antisymm ?_ hge⟩
    rw [← hNk'] at hle; exact hle
  exact (core hr hr2 hN a ha0 hsum hsq).1

end CFSG.GroupTheory.CoprimeActionSupport.ShultMultiplicityArithmetic
