module

public import Mathlib.GroupTheory.Perm.Centralizer

public section

namespace CFSG.EvenSporadicStandard.HSStd.HFI

open Equiv Equiv.Perm Subgroup

theorem exists_card_centralizer_involution {n : ℕ} {σ : Perm (Fin n)} (h2 : σ * σ = 1)
    (h1 : σ ≠ 1) :
    ∃ m : ℕ, 1 ≤ m ∧ 2 * m ≤ n ∧
      Nat.card (centralizer ({σ} : Set (Perm (Fin n)))) =
        (n - 2 * m).factorial * 2 ^ m * m.factorial ∧ Perm.sign σ = (-1) ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rwa [sq]) h1
  have hct : ∀ k ∈ σ.cycleType, k = 2 := by
    intro k hk
    have hdvd : k ∣ orderOf σ := by
      rw [← Equiv.Perm.lcm_cycleType]
      exact Multiset.dvd_lcm hk
    rw [hord] at hdvd
    exact (Nat.le_of_dvd (by norm_num) hdvd).antisymm (Equiv.Perm.two_le_of_mem_cycleType hk)
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate_of_mem hct
  set m := Multiset.card σ.cycleType with hm
  have hm1 : 1 ≤ m := by
    rw [Nat.one_le_iff_ne_zero, hm, Ne, Multiset.card_eq_zero, Equiv.Perm.cycleType_eq_zero]
    exact h1
  have hsum : σ.cycleType.sum = 2 * m := by
    rw [hrep, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hle : 2 * m ≤ n := by
    rw [← hsum, Equiv.Perm.sum_cycleType]
    calc σ.support.card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  refine ⟨m, hm1, hle, ?_, ?_⟩
  · rw [Equiv.Perm.nat_card_centralizer, hsum, Fintype.card_fin]
    have hprod : σ.cycleType.prod = 2 ^ m := by
      rw [hrep, Multiset.prod_replicate]
    have hfin : σ.cycleType.toFinset = {2} := by
      rw [hrep]
      ext k
      simp only [Multiset.mem_toFinset, Multiset.mem_replicate, Finset.mem_singleton]
      constructor
      · rintro ⟨-, rfl⟩; rfl
      · rintro rfl; exact ⟨by omega, rfl⟩
    rw [hprod, hfin, Finset.prod_singleton]
    have hcount : σ.cycleType.count 2 = m := by
      rw [hrep, Multiset.count_replicate_self]
    rw [hcount]
  · rw [Equiv.Perm.sign_of_cycleType, hsum, ← hm]
    rw [show 2 * m + m = 2 * m + m from rfl, pow_add, pow_mul, neg_one_sq, one_pow, one_mul]

end CFSG.EvenSporadicStandard.HSStd.HFI
