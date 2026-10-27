module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Data.Nat.Totient
public import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG.GH74.Generic.BProg.B3.S3SL2Perm

open Equiv Equiv.Perm Subgroup

variable {n : ℕ}

theorem cycleType_involution {σ : Perm (Fin n)} (hσ : σ * σ = 1) :
    σ.cycleType = Multiset.replicate (σ.cycleType.card) 2 := by
  have hord : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hσ)
  refine Multiset.eq_replicate_card.2 fun m hm => ?_
  have h1 : m ∣ orderOf σ := Equiv.Perm.dvd_of_mem_cycleType hm
  have h2 : 2 ≤ m := Equiv.Perm.two_le_of_mem_cycleType hm
  have h3 : m ∣ 2 := h1.trans hord
  have := Nat.le_of_dvd (by norm_num) h3
  omega

theorem card_support_involution {σ : Perm (Fin n)} (hσ : σ * σ = 1) :
    σ.support.card = 2 * σ.cycleType.card := by
  rw [← Equiv.Perm.sum_cycleType, cycleType_involution hσ]
  simp [Multiset.sum_replicate, mul_comm]

theorem sign_involution {σ : Perm (Fin n)} (hσ : σ * σ = 1) :
    Perm.sign σ = (-1) ^ σ.cycleType.card := by
  rw [Equiv.Perm.sign_of_cycleType, cycleType_involution hσ]
  simp only [Multiset.sum_replicate, smul_eq_mul, Multiset.card_replicate]
  rw [pow_add, Even.neg_one_pow ⟨σ.cycleType.card, by ring⟩, one_mul]

theorem card_centralizer_involution {σ : Perm (Fin n)} (hσ : σ * σ = 1) (hσ1 : σ ≠ 1) :
    Nat.card (centralizer ({σ} : Set (Perm (Fin n)))) =
      (n - 2 * σ.cycleType.card).factorial * 2 ^ σ.cycleType.card * σ.cycleType.card.factorial := by
  rw [Equiv.Perm.nat_card_centralizer]
  have hk : 0 < σ.cycleType.card := by
    rw [Multiset.card_pos]
    intro h0
    apply hσ1
    exact Equiv.Perm.cycleType_eq_zero.1 h0
  have hct := cycleType_involution hσ
  set k := σ.cycleType.card with hkdef
  rw [hct]
  simp [Multiset.sum_replicate, Multiset.prod_replicate, Multiset.toFinset_replicate, hk.ne', Multiset.count_replicate]
  left
  rw [Nat.mul_comm k 2]

theorem exists_swap_mul_swap {σ : Perm (Fin n)} (hσ : σ * σ = 1) (h4 : σ.support.card = 4) :
    ∃ a b c d : Fin n, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      σ = swap a b * swap c d := by
  classical
  have hne : σ.support.Nonempty := by rw [← Finset.card_pos, h4]; norm_num
  obtain ⟨a, ha⟩ := hne
  have ha' : a ∈ σ.support := ha
  rw [Equiv.Perm.mem_support] at ha
  obtain ⟨b, hb⟩ : ∃ b, b = σ a := ⟨_, rfl⟩
  have hab : a ≠ b := fun h => ha (by rw [hb] at h; exact h.symm)
  have hσb : σ b = a := by
    have : (σ * σ) a = a := by rw [hσ]; rfl
    simpa [Perm.mul_apply, ← hb] using this
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  have hcomm : swap a b * σ = σ * swap a b := by
    rw [Equiv.swap_mul_eq_mul_swap, hσinv, swap_comm]
    have h1 : σ a = b := hb.symm
    rw [h1, hσb]
  obtain ⟨σ', hσ'⟩ : ∃ σ' : Perm (Fin n), σ' = swap a b * σ := ⟨_, rfl⟩
  have hσ'a : σ' a = a := by simp [hσ', Perm.mul_apply, ← hb]
  have hσ'b : σ' b = b := by simp [hσ', Perm.mul_apply, hσb]
  have hσ'2 : σ' * σ' = 1 := by
    have h2 : swap a b * swap a b = 1 := swap_mul_self a b
    calc σ' * σ' = swap a b * σ * (swap a b * σ) := by rw [hσ']
      _ = swap a b * (σ * swap a b) * σ := by simp only [mul_assoc]
      _ = swap a b * (swap a b * σ) * σ := by rw [hcomm]
      _ = (swap a b * swap a b) * (σ * σ) := by simp only [mul_assoc]
      _ = 1 := by rw [h2, hσ, one_mul]
  have hb' : b ∈ σ.support.erase a := by
    simp [Finset.mem_erase, Equiv.Perm.mem_support, hab.symm, hσb, hab]
  have hsupp : σ'.support ⊆ ((σ.support.erase a).erase b) := by
    intro x hx
    rw [Equiv.Perm.mem_support] at hx
    have hxa : x ≠ a := fun h => hx (h ▸ hσ'a)
    have hxb : x ≠ b := fun h => hx (h ▸ hσ'b)
    have hxσ : σ x ≠ x := by
      intro h
      apply hx
      simp [hσ', Perm.mul_apply, h, swap_apply_of_ne_of_ne hxa hxb]
    simp [Finset.mem_erase, hxa, hxb, Equiv.Perm.mem_support, hxσ]
  have hcard2 : σ'.support.card ≤ 2 := by
    have h1 := Finset.card_le_card hsupp
    rw [Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha', h4] at h1
    simpa using h1
  have hne1 : σ' ≠ 1 := by
    intro h1
    have hσs : σ = swap a b := by
      have : swap a b * σ = 1 := hσ' ▸ h1
      calc σ = swap a b * (swap a b * σ) := (swap_mul_self_mul a b σ).symm
        _ = swap a b := by rw [this, mul_one]
    rw [hσs, Equiv.Perm.card_support_swap hab] at h4
    omega
  have h2 : 2 ≤ σ'.support.card := Equiv.Perm.two_le_card_support_of_ne_one hne1
  have hsw : σ'.IsSwap := Equiv.Perm.card_support_eq_two.1 (le_antisymm hcard2 h2)
  obtain ⟨c, d, hcd, hσ'cd⟩ := hsw
  have hc : c ∈ σ'.support := by
    rw [Equiv.Perm.mem_support, hσ'cd]; simpa using hcd.symm
  have hd : d ∈ σ'.support := by
    rw [Equiv.Perm.mem_support, hσ'cd]; simpa using hcd
  have hc' := hsupp hc
  have hd' := hsupp hd
  simp only [Finset.mem_erase] at hc' hd'
  refine ⟨a, b, c, d, hab, hc'.2.1.symm, hd'.2.1.symm, hc'.1.symm, hd'.1.symm, hcd, ?_⟩
  calc σ = swap a b * (swap a b * σ) := (swap_mul_self_mul a b σ).symm
    _ = swap a b * swap c d := by rw [← hσ', hσ'cd]

theorem prime_ge_five_dvd {q : ℕ} (hq : Odd q) (h5 : 5 ≤ q) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ q * (q ^ 2 - 1) := by
  by_contra hcon
  push Not at hcon
  have hsmall : ∀ d : ℕ, d.Prime → d ∣ q * (q ^ 2 - 1) → d = 2 ∨ d = 3 := by
    intro d hd hdvd
    by_contra hd23
    push Not at hd23
    have := hd.two_le
    have h4 : d ≠ 4 := fun h => by rw [h] at hd; norm_num at hd
    have : 5 ≤ d := by omega
    exact hcon d hd this hdvd
  have hq0 : q ≠ 0 := by omega
  have hq3 : q = 3 ^ q.primeFactorsList.length := by
    refine Nat.eq_prime_pow_of_unique_prime_dvd hq0 ?_
    intro d hd hdq
    rcases hsmall d hd (Dvd.dvd.mul_right hdq _) with h | h
    · exfalso
      subst h
      exact (Nat.not_even_iff_odd.2 hq) (even_iff_two_dvd.2 hdq)
    · exact h
  set f := q.primeFactorsList.length with hf
  have hf1 : 1 ≤ f := by
    by_contra h0
    push Not at h0
    have : f = 0 := by omega
    rw [this] at hq3
    omega
  have h3q : 3 ∣ q := by rw [hq3]; exact dvd_pow_self 3 (by omega)
  have hq2 : q ^ 2 - 1 ≠ 0 := by
    have : 25 ≤ q ^ 2 := by nlinarith
    omega
  have hq2pow : q ^ 2 - 1 = 2 ^ (q ^ 2 - 1).primeFactorsList.length := by
    refine Nat.eq_prime_pow_of_unique_prime_dvd hq2 ?_
    intro d hd hdq
    rcases hsmall d hd (Dvd.dvd.mul_left hdq _) with h | h
    · exact h
    · exfalso
      subst h
      have h1 : 3 ∣ q ^ 2 := dvd_pow h3q (by norm_num)
      have h2 : q ^ 2 - 1 + 1 = q ^ 2 := by omega
      have : 3 ∣ 1 := (Nat.dvd_add_right hdq).1 (h2 ▸ h1)
      omega
  set e := (q ^ 2 - 1).primeFactorsList.length
  have hfac : (q - 1) * (q + 1) = 2 ^ e := by
    rw [← hq2pow]
    have : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      have h1 : 1 ≤ q := by omega
      obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
      simp
      ring_nf
      omega
    rw [this]
  have h1 : q - 1 ∣ 2 ^ e := Dvd.intro _ hfac
  have h2 : q + 1 ∣ 2 ^ e := Dvd.intro_left _ hfac
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have hi2 : 2 ≤ i := by
    by_contra h0
    push Not at h0
    interval_cases i <;> simp at hi' <;> omega
  have hj2 : 2 ≤ j := by
    by_contra h0
    push Not at h0
    interval_cases j <;> simp at hj' <;> omega
  have h4i : 4 ∣ q - 1 := by rw [hi']; exact (pow_dvd_pow 2 hi2)
  have h4j : 4 ∣ q + 1 := by rw [hj']; exact (pow_dvd_pow 2 hj2)
  omega

theorem prime_dvd_cases {m k r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r)
    (h : r ∣ m.factorial * 2 ^ k * k.factorial) : r ≤ m ∨ r ≤ k := by
  rcases (Nat.Prime.dvd_mul hr).1 h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hr).1 h1 with h2 | h2
    · exact Or.inl ((Nat.Prime.dvd_factorial hr).1 h2)
    · exfalso
      have := Nat.le_of_dvd (by norm_num) (hr.dvd_of_dvd_pow h2)
      omega
  · exact Or.inr ((Nat.Prime.dvd_factorial hr).1 h1)


end CFSG.GH74.Generic.BProg.B3.S3SL2Perm
