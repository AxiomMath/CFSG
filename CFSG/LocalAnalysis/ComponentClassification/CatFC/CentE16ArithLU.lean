module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

theorem e16_four_dvd_pow_sub_one {q : ℕ} (hq : q % 4 = 1) (i : ℕ) : 4 ∣ q ^ i - 1 := by
  have h1 : q - 1 ∣ q ^ i - 1 ^ i := Nat.sub_dvd_pow_sub_pow q 1 i
  rw [one_pow] at h1
  have h2 : 4 ∣ q - 1 := by omega
  exact h2.trans h1

theorem e16_eight_dvd_sq_sub_one {q : ℕ} (hq : q % 4 = 1) : 8 ∣ q ^ 2 - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, q = 4 * k + 1 := ⟨q / 4, by omega⟩
  refine ⟨2 * k ^ 2 + k, ?_⟩
  have h : (4 * k + 1) ^ 2 = 8 * (2 * k ^ 2 + k) + 1 := by ring
  omega

theorem e16_two_dvd_pow_add_one {q : ℕ} (hq : q % 4 = 1) (i : ℕ) : 2 ∣ q ^ i + 1 := by
  obtain ⟨k, hk⟩ := (Odd.pow (Nat.odd_iff.mpr (by omega : q % 2 = 1)) : Odd (q ^ i))
  exact ⟨k + 1, by omega⟩

theorem e16_two_pow_bound {a n : ℕ} (hn : 3 ≤ n) (h : 2 ^ a ∣ n) :
    5 + a ≤ 2 * (n - 2) + 3 := by
  have h1 : a < n := lt_of_lt_of_le Nat.lt_two_pow_self (Nat.le_of_dvd (by omega) h)
  rcases Nat.lt_or_ge n 5 with h5 | h5
  · interval_cases n <;> interval_cases a <;> (first | omega | norm_num at h)
  · omega

theorem e16_two_pow_dvd_prod_sub_one {q : ℕ} (hq : q % 4 = 1) (m : ℕ) :
    2 ^ (2 * m + 3) ∣ ∏ i ∈ Finset.Icc 2 (m + 2), (q ^ i - 1) := by
  induction m with
  | zero =>
    have h8 := e16_eight_dvd_sq_sub_one hq
    norm_num [Finset.Icc_self]
    exact h8
  | succ m ih =>
    rw [show m + 1 + 2 = m + 2 + 1 by omega,
      Finset.prod_Icc_succ_top (by omega : 2 ≤ m + 2 + 1)]
    have e : 2 ^ (2 * (m + 1) + 3) = 2 ^ (2 * m + 3) * 4 := by ring
    rw [e]
    exact mul_dvd_mul ih (e16_four_dvd_pow_sub_one hq _)

theorem e16_two_pow_six_dvd_psu_prod {q : ℕ} (hq : q % 4 = 1) {n : ℕ} (hn : 4 ≤ n) :
    2 ^ 6 ∣ ∏ i ∈ Finset.Icc 2 n, (if Even i then q ^ i - 1 else q ^ i + 1) := by
  induction n, hn using Nat.le_induction with
  | base =>
    have e : Finset.Icc 2 4 = {2, 3, 4} := by decide
    have h2 : (2 : ℕ) ∉ ({3, 4} : Finset ℕ) := by decide
    have h3 : (3 : ℕ) ∉ ({4} : Finset ℕ) := by decide
    rw [e, Finset.prod_insert h2, Finset.prod_insert h3, Finset.prod_singleton]
    have e2 : (if Even (2 : ℕ) then q ^ 2 - 1 else q ^ 2 + 1) = q ^ 2 - 1 := if_pos even_two
    have e3 : (if Even (3 : ℕ) then q ^ 3 - 1 else q ^ 3 + 1) = q ^ 3 + 1 :=
      if_neg (by decide)
    have e4 : (if Even (4 : ℕ) then q ^ 4 - 1 else q ^ 4 + 1) = q ^ 4 - 1 :=
      if_pos (by decide)
    rw [e2, e3, e4]
    have h8 := e16_eight_dvd_sq_sub_one hq
    have h2' := e16_two_dvd_pow_add_one hq 3
    have h4 := e16_four_dvd_pow_sub_one hq 4
    have e64 : (2 : ℕ) ^ 6 = 8 * (2 * 4) := by norm_num
    rw [e64]
    exact mul_dvd_mul h8 (mul_dvd_mul h2' h4)
  | succ n hn ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ n + 1)]
    exact ih.trans (dvd_mul_right _ _)

theorem e16_arith_psl {n q : ℕ} (hq : q % 4 = 1) (hn : 3 ≤ n) :
    2 ^ 5 * lieOrderDivisor .PSL n q ∣ lieOrderNumerator .PSL n q := by
  show 2 ^ 5 * Nat.gcd n (q - 1) ∣ q ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1)
  apply Dvd.dvd.mul_left
  have hg0 : Nat.gcd n (q - 1) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (by omega)).ne'
  obtain ⟨a, g', hg'odd, hg⟩ := Nat.exists_eq_two_pow_mul_odd hg0
  have h2g : 2 ^ a ∣ Nat.gcd n (q - 1) := ⟨g', hg⟩
  have h2a : 2 ^ a ∣ n := h2g.trans (Nat.gcd_dvd_left n (q - 1))
  have hg'g : g' ∣ Nat.gcd n (q - 1) := Dvd.intro_left (2 ^ a) hg.symm
  have hq1 : q - 1 ∣ q ^ 2 - 1 := Nat.sub_one_dvd_pow_sub_one q 2
  have h2mem : (2 : ℕ) ∈ Finset.Icc 2 n := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have hq2 : q ^ 2 - 1 ∣ ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) :=
    Finset.dvd_prod_of_mem (fun i => q ^ i - 1) h2mem
  have hg'P : g' ∣ ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) :=
    ((hg'g.trans (Nat.gcd_dvd_right n (q - 1))).trans hq1).trans hq2
  have hpow : 2 ^ (5 + a) ∣ ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) := by
    have h := e16_two_pow_dvd_prod_sub_one hq (n - 2)
    rw [show n - 2 + 2 = n by omega] at h
    exact (pow_dvd_pow 2 (e16_two_pow_bound hn h2a)).trans h
  have hcop : Nat.Coprime (2 ^ (5 + a)) g' :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hg'odd.not_two_dvd_nat)
  have key : 2 ^ 5 * Nat.gcd n (q - 1) = 2 ^ (5 + a) * g' := by
    rw [hg]; ring
  rw [key]
  exact hcop.mul_dvd_of_dvd_of_dvd hpow hg'P

theorem e16_arith_psu {n q : ℕ} (hq : q % 4 = 1) (hn : 4 ≤ n) :
    2 ^ 5 * lieOrderDivisor .PSU n q ∣ lieOrderNumerator .PSU n q := by
  show 2 ^ 5 * Nat.gcd n (q + 1) ∣
    q ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, (if Even i then q ^ i - 1 else q ^ i + 1)
  apply Dvd.dvd.mul_left
  have hg0 : Nat.gcd n (q + 1) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (by omega)).ne'
  obtain ⟨a, g', hg'odd, hg⟩ := Nat.exists_eq_two_pow_mul_odd hg0
  have h2g : 2 ^ a ∣ Nat.gcd n (q + 1) := ⟨g', hg⟩
  have ha : a ≤ 1 := by
    by_contra hcon
    have h4 : 2 ^ 2 ∣ q + 1 :=
      (pow_dvd_pow 2 (by omega : 2 ≤ a)).trans (h2g.trans (Nat.gcd_dvd_right n (q + 1)))
    norm_num at h4
    omega
  have hg'g : g' ∣ Nat.gcd n (q + 1) := Dvd.intro_left (2 ^ a) hg.symm
  have hq3 : q + 1 ∣ q ^ 3 + 1 := by
    have h := Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 3)
    rwa [one_pow] at h
  have h3mem : (3 : ℕ) ∈ Finset.Icc 2 n := Finset.mem_Icc.2 ⟨by norm_num, by omega⟩
  have e3 : (if Even (3 : ℕ) then q ^ 3 - 1 else q ^ 3 + 1) = q ^ 3 + 1 :=
    if_neg (by decide)
  have hF3 : q ^ 3 + 1 ∣ ∏ i ∈ Finset.Icc 2 n, (if Even i then q ^ i - 1 else q ^ i + 1) := by
    have h := Finset.dvd_prod_of_mem (fun i => if Even i then q ^ i - 1 else q ^ i + 1) h3mem
    rw [e3] at h
    exact h
  have hg'P : g' ∣ ∏ i ∈ Finset.Icc 2 n, (if Even i then q ^ i - 1 else q ^ i + 1) :=
    ((hg'g.trans (Nat.gcd_dvd_right n (q + 1))).trans hq3).trans hF3
  have hpow : 2 ^ (5 + a) ∣ ∏ i ∈ Finset.Icc 2 n, (if Even i then q ^ i - 1 else q ^ i + 1) :=
    (pow_dvd_pow 2 (by omega : 5 + a ≤ 6)).trans (e16_two_pow_six_dvd_psu_prod hq hn)
  have hcop : Nat.Coprime (2 ^ (5 + a)) g' :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hg'odd.not_two_dvd_nat)
  have key : 2 ^ 5 * Nat.gcd n (q + 1) = 2 ^ (5 + a) * g' := by
    rw [hg]; ring
  rw [key]
  exact hcop.mul_dvd_of_dvd_of_dvd hpow hg'P

theorem e16_arith_psu_three {q : ℕ} (hq : q % 4 = 1) :
    2 ^ 4 * lieOrderDivisor .PSU 3 q ∣ lieOrderNumerator .PSU 3 q := by
  show 2 ^ 4 * Nat.gcd 3 (q + 1) ∣
    q ^ (3 * (3 - 1) / 2) * ∏ i ∈ Finset.Icc 2 3, (if Even i then q ^ i - 1 else q ^ i + 1)
  apply Dvd.dvd.mul_left
  have e : Finset.Icc 2 3 = {2, 3} := by decide
  have h23 : (2 : ℕ) ∉ ({3} : Finset ℕ) := by decide
  rw [e, Finset.prod_insert h23, Finset.prod_singleton]
  have e2 : (if Even (2 : ℕ) then q ^ 2 - 1 else q ^ 2 + 1) = q ^ 2 - 1 := if_pos even_two
  have e3 : (if Even (3 : ℕ) then q ^ 3 - 1 else q ^ 3 + 1) = q ^ 3 + 1 :=
    if_neg (by decide)
  rw [e2, e3]
  have hq3 : q + 1 ∣ q ^ 3 + 1 := by
    have h := Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 3)
    rwa [one_pow] at h
  have h16 : 2 ^ 4 ∣ (q ^ 2 - 1) * (q ^ 3 + 1) := by
    have h8 := e16_eight_dvd_sq_sub_one hq
    have h2 := e16_two_dvd_pow_add_one hq 3
    have e16 : (2 : ℕ) ^ 4 = 8 * 2 := by norm_num
    rw [e16]
    exact mul_dvd_mul h8 h2
  have hcop : Nat.Coprime (2 ^ 4) (Nat.gcd 3 (q + 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 (q + 1)) (by norm_num)
  have hgP : Nat.gcd 3 (q + 1) ∣ (q ^ 2 - 1) * (q ^ 3 + 1) :=
    ((Nat.gcd_dvd_right 3 (q + 1)).trans hq3).trans (dvd_mul_left _ _)
  exact hcop.mul_dvd_of_dvd_of_dvd h16 hgP

end CFSG.ComponentClassification.CatFC
