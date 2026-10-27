module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

namespace FTG

open Subgroup Equiv

theorem card_centralizer_lt_of_even_involution {n : ℕ} (hn : n ≤ 9) {c : Perm (Fin n)}
    (hc2 : c * c = 1) (hc1 : c ≠ 1) (hsign : Perm.sign c = 1) :
    Nat.card (centralizer ({c} : Set (Perm (Fin n)))) < 2520 := by
  classical
  have hord : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hc2)
  have hall : ∀ m ∈ c.cycleType, m = 2 := by
    intro m hm
    have h1 := (Perm.dvd_of_mem_cycleType hm).trans hord
    have h2 := Perm.two_le_of_mem_cycleType hm
    have h3 := Nat.le_of_dvd (by norm_num) h1
    omega
  set k := Multiset.card c.cycleType with hk
  have hct : c.cycleType = Multiset.replicate k 2 := Multiset.eq_replicate.mpr ⟨rfl, hall⟩
  have hsum : c.cycleType.sum = 2 * k := by
    rw [hct, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      apply hc1
      rw [← Perm.cycleType_eq_zero, hct, h0, Multiset.replicate_zero]
    · exact h0
  have hle : 2 * k ≤ n := by
    rw [← hsum, Perm.sum_cycleType]
    simpa using Finset.card_le_univ c.support
  have heven : Even k := by
    have hs := Perm.sign_of_cycleType c
    rw [hsign, hsum] at hs
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have : Odd (2 * k + k) := by
      rw [show 2 * k + k = 2 * k + k from rfl]
      exact Even.add_odd (even_two_mul k) hodd
    rw [this.neg_one_pow] at hs
    exact absurd hs (by decide)
  rw [Perm.nat_card_centralizer, hsum, hct, Multiset.prod_replicate, Fintype.card_fin]
  have hfin : (Multiset.replicate k 2).toFinset = {2} := by
    have hk0 : k ≠ 0 := by omega
    simp [Multiset.toFinset_replicate, hk0]
  rw [hfin, Finset.prod_singleton, Multiset.count_replicate_self]
  obtain ⟨j, hj⟩ := heven
  have hk4 : k = 2 ∨ k = 4 := by omega
  rcases hk4 with h | h
  · rw [h]
    have hf : (n - 2 * 2).factorial ≤ (5 : ℕ).factorial := Nat.factorial_le (by omega)
    have : (5 : ℕ).factorial = 120 := by decide
    calc (n - 2 * 2).factorial * 2 ^ 2 * (2 : ℕ).factorial ≤ 120 * 2 ^ 2 * 2 := by
          rw [show (2 : ℕ).factorial = 2 from rfl]
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (this ▸ hf))
      _ < 2520 := by norm_num
  · rw [h]
    have hf : (n - 2 * 4).factorial ≤ (1 : ℕ).factorial := Nat.factorial_le (by omega)
    calc (n - 2 * 4).factorial * 2 ^ 4 * (4 : ℕ).factorial ≤ 1 * 2 ^ 4 * 24 := by
          rw [show (4 : ℕ).factorial = 24 from rfl]
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hf)
      _ < 2520 := by norm_num

theorem exists_pair_of_card_four {Q : Type*} [Group Q] [Finite Q] (hQ : Nat.card Q = 4) :
    ∃ u r : Q, orderOf u = 2 ∧ r ∉ zpowers u ∧ r ^ 2 ∈ zpowers u ∧ r * u = u * r := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcm : IsMulCommutative Q :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hQ]; norm_num)
  have hcomm : ∀ a b : Q, a * b = b * a := fun a b => hcm.is_comm.comm a b
  by_cases h4 : ∃ r : Q, orderOf r = 4
  · obtain ⟨r, hr⟩ := h4
    have hu : orderOf (r ^ 2) = 2 := by
      rw [orderOf_pow' r (by norm_num), hr]
      norm_num
    refine ⟨r ^ 2, r, hu, ?_, Subgroup.mem_zpowers _, hcomm _ _⟩
    intro hmem
    have h1 : orderOf r ∣ orderOf (r ^ 2) := orderOf_dvd_of_mem_zpowers hmem
    rw [hr, hu] at h1
    exact absurd h1 (by norm_num)
  · push Not at h4
    have hsq : ∀ x : Q, x ^ 2 = 1 := by
      intro x
      have hx : orderOf x ∣ 4 := hQ ▸ orderOf_dvd_natCard x
      have hx4 := h4 x
      have : orderOf x ∣ 2 := by
        have hdivs : orderOf x = 1 ∨ orderOf x = 2 ∨ orderOf x = 4 := by
          have hle := Nat.le_of_dvd (by norm_num) hx
          interval_cases h : orderOf x <;> simp_all
        rcases hdivs with h | h | h
        · rw [h]; exact one_dvd 2
        · rw [h]
        · exact absurd h hx4
      exact orderOf_dvd_iff_pow_eq_one.mp this
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [hQ]; norm_num)
    have hcu : Nat.card (zpowers u) = 2 := by rw [Nat.card_zpowers, hu]
    have hne : (zpowers u : Set Q) ≠ Set.univ := by
      intro h
      have : Nat.card (zpowers u) = Nat.card Q := by
        rw [← Nat.card_univ (α := Q), ← h]
        rfl
      rw [hcu, hQ] at this
      exact absurd this (by norm_num)
    obtain ⟨r, hr⟩ : ∃ r : Q, r ∉ zpowers u := by
      by_contra hall
      push Not at hall
      exact hne (Set.eq_univ_of_forall hall)
    refine ⟨u, r, hu, hr, ?_, hcomm _ _⟩
    rw [hsq r]
    exact one_mem _

end FTG

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
