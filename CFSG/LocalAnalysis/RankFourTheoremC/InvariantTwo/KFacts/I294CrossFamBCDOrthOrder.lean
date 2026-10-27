module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDSp

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open

section Order

variable {p Q e : ℕ} [hp : Fact p.Prime]

theorem padicValNat_div_of_dvd {A g : ℕ} (hg : g ∣ A) (hpg : ¬ p ∣ g) (hA : A ≠ 0) :
    padicValNat p (A / g) = padicValNat p A := by
  have hg0 : g ≠ 0 := fun h => hA (by rw [h, zero_dvd_iff] at hg; exact hg)
  have h1 : A = A / g * g := (Nat.div_mul_cancel hg).symm
  have h2 : A / g ≠ 0 := fun h => hA (by rw [h1, h, zero_mul])
  conv_rhs => rw [h1]
  rw [padicValNat.mul h2 hg0, padicValNat.eq_zero_of_not_dvd hpg, add_zero]

theorem padicValNat_sq_sub_one_eq (hp5 : 5 ≤ p) (heo : Odd e)
    (hpe : ∀ j : ℕ, p ∣ Q ^ j - 1 ↔ e ∣ j) (hQ : 1 < Q) {j : ℕ} (hj : 1 ≤ j) :
    padicValNat p (Q ^ (2 * j) - 1) = padicValNat p (Q ^ j - 1) := by
  have hqj : 1 ≤ Q ^ j := Nat.one_le_pow _ _ (by omega)
  have hfac : Q ^ (2 * j) - 1 = (Q ^ j + 1) * (Q ^ j - 1) := by
    rw [mul_comm, pow_mul]
    have := Nat.sq_sub_sq (Q ^ j) 1
    simpa using this
  have hlt : 0 < Q ^ j - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) hQ)
  rw [hfac, padicValNat.mul (by omega) hlt.ne',
    padicValNat.eq_zero_of_not_dvd (not_dvd_pow_add_one_of_odd hp5 heo hpe j (by omega)),
    zero_add]

theorem padicValNat_prod_sq_sub_one (hp5 : 5 ≤ p) (heo : Odd e)
    (hpe : ∀ j : ℕ, p ∣ Q ^ j - 1 ↔ e ∣ j) (hQ : 1 < Q) (n : ℕ) :
    padicValNat p (∏ i ∈ Finset.Icc 1 n, (Q ^ (2 * i) - 1)) =
      ∑ j ∈ Finset.Ioc 0 n, padicValNat p (Q ^ j - 1) := by
  have hne : ∀ j ∈ Finset.Icc 1 n, Q ^ (2 * j) - 1 ≠ 0 := fun j hj =>
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by have := (Finset.mem_Icc.1 hj).1; omega) hQ)
  rw [padicValNat_prod_finset hne]
  have hIcc : Finset.Icc 1 n = Finset.Ioc 0 n := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hIcc]
  exact Finset.sum_congr rfl fun j hj =>
    padicValNat_sq_sub_one_eq hp5 heo hpe hQ (Finset.mem_Ioc.1 hj).1

theorem not_dvd_gcd_four (hp5 : 5 ≤ p) (x : ℕ) : ¬ p ∣ Nat.gcd 4 x := fun h =>
  absurd (Nat.le_of_dvd (by norm_num) (h.trans (Nat.gcd_dvd_left 4 x))) (by omega)

theorem not_dvd_gcd_two (hp5 : 5 ≤ p) (x : ℕ) : ¬ p ∣ Nat.gcd 2 x := fun h =>
  absurd (Nat.le_of_dvd (by norm_num) (h.trans (Nat.gcd_dvd_left 2 x))) (by omega)

theorem padicValNat_ordBC (hp5 : 5 ≤ p) (heo : Odd e) (hpe : ∀ j : ℕ, p ∣ Q ^ j - 1 ↔ e ∣ j)
    (hpQ : ¬ p ∣ Q) (hQ : 1 < Q) {r : ℕ} (hr : 1 ≤ r) :
    padicValNat p (ordBC r Q) = ∑ j ∈ Finset.Ioc 0 r, padicValNat p (Q ^ j - 1) := by
  have hne : ∀ j ∈ Finset.Icc 1 r, Q ^ (2 * j) - 1 ≠ 0 := fun j hj =>
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by have := (Finset.mem_Icc.1 hj).1; omega) hQ)
  have hprod0 : ∏ i ∈ Finset.Icc 1 r, (Q ^ (2 * i) - 1) ≠ 0 := Finset.prod_ne_zero_iff.2 hne
  have hA : Q ^ (r * r) * ∏ i ∈ Finset.Icc 1 r, (Q ^ (2 * i) - 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by omega)) hprod0
  have hdvd : Nat.gcd 2 (Q - 1) ∣ Q ^ (r * r) * ∏ i ∈ Finset.Icc 1 r, (Q ^ (2 * i) - 1) := by
    have h1 : Nat.gcd 2 (Q - 1) ∣ Q - 1 := Nat.gcd_dvd_right _ _
    have h2 : Q - 1 ∣ Q ^ (2 * 1) - 1 := by simpa using Nat.sub_dvd_pow_sub_pow Q 1 2
    have h3 : Q ^ (2 * 1) - 1 ∣ ∏ i ∈ Finset.Icc 1 r, (Q ^ (2 * i) - 1) :=
      Finset.dvd_prod_of_mem (fun i => Q ^ (2 * i) - 1) (Finset.mem_Icc.2 ⟨le_rfl, hr⟩)
    exact Dvd.dvd.mul_left (h1.trans (h2.trans h3)) _
  unfold ordBC
  rw [padicValNat_div_of_dvd hdvd (not_dvd_gcd_two hp5 _) hA,
    padicValNat.mul (pow_ne_zero _ (by omega)) hprod0,
    padicValNat.eq_zero_of_not_dvd (fun h => hpQ (hp.out.dvd_of_dvd_pow h)), zero_add,
    padicValNat_prod_sq_sub_one hp5 heo hpe hQ]

theorem padicValNat_ordD (hp5 : 5 ≤ p) (heo : Odd e) (hpe : ∀ j : ℕ, p ∣ Q ^ j - 1 ↔ e ∣ j)
    (hpQ : ¬ p ∣ Q) (hQ : 1 < Q) {r : ℕ} (hr : 1 ≤ r) :
    padicValNat p (ordD r Q) = ∑ j ∈ Finset.Ioc 0 r, padicValNat p (Q ^ j - 1) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hne : ∀ j ∈ Finset.Icc 1 r', Q ^ (2 * j) - 1 ≠ 0 := fun j hj =>
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by have := (Finset.mem_Icc.1 hj).1; omega) hQ)
  have hprod0 : ∏ i ∈ Finset.Icc 1 r', (Q ^ (2 * i) - 1) ≠ 0 := Finset.prod_ne_zero_iff.2 hne
  have hr1 : Q ^ (r' + 1) - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) hQ)
  have hA : Q ^ ((r' + 1) * (r' + 1 - 1)) * (Q ^ (r' + 1) - 1) *
      ∏ i ∈ Finset.Icc 1 (r' + 1 - 1), (Q ^ (2 * i) - 1) ≠ 0 := by
    rw [Nat.add_sub_cancel]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by omega)) hr1) hprod0
  have hdvd : Nat.gcd 4 (Q ^ (r' + 1) - 1) ∣ Q ^ ((r' + 1) * (r' + 1 - 1)) * (Q ^ (r' + 1) - 1) *
      ∏ i ∈ Finset.Icc 1 (r' + 1 - 1), (Q ^ (2 * i) - 1) :=
    Dvd.dvd.mul_right (Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) _) _
  unfold ordD
  rw [padicValNat_div_of_dvd hdvd (not_dvd_gcd_four hp5 _) hA, Nat.add_sub_cancel] at *
  rw [padicValNat.mul (mul_ne_zero (pow_ne_zero _ (by omega)) hr1) hprod0,
    padicValNat.mul (pow_ne_zero _ (by omega)) hr1,
    padicValNat.eq_zero_of_not_dvd (fun h => hpQ (hp.out.dvd_of_dvd_pow h)), zero_add,
    padicValNat_prod_sq_sub_one hp5 heo hpe hQ, Finset.sum_Ioc_succ_top (Nat.zero_le r'),
    add_comm]

theorem padicValNat_ordTwistedD (hp5 : 5 ≤ p) (heo : Odd e)
    (hpe : ∀ j : ℕ, p ∣ Q ^ j - 1 ↔ e ∣ j) (hpQ : ¬ p ∣ Q) (hQ : 1 < Q) {r : ℕ} (hr : 1 ≤ r) :
    padicValNat p (ordTwistedD r Q) = ∑ j ∈ Finset.Ioc 0 (r - 1), padicValNat p (Q ^ j - 1) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hne : ∀ j ∈ Finset.Icc 1 r', Q ^ (2 * j) - 1 ≠ 0 := fun j hj =>
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by have := (Finset.mem_Icc.1 hj).1; omega) hQ)
  have hprod0 : ∏ i ∈ Finset.Icc 1 r', (Q ^ (2 * i) - 1) ≠ 0 := Finset.prod_ne_zero_iff.2 hne
  have hr1 : Q ^ (r' + 1) + 1 ≠ 0 := by omega
  have hA : Q ^ ((r' + 1) * (r' + 1 - 1)) * (Q ^ (r' + 1) + 1) *
      ∏ i ∈ Finset.Icc 1 (r' + 1 - 1), (Q ^ (2 * i) - 1) ≠ 0 := by
    rw [Nat.add_sub_cancel]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by omega)) hr1) hprod0
  have hdvd : Nat.gcd 4 (Q ^ (r' + 1) + 1) ∣ Q ^ ((r' + 1) * (r' + 1 - 1)) * (Q ^ (r' + 1) + 1) *
      ∏ i ∈ Finset.Icc 1 (r' + 1 - 1), (Q ^ (2 * i) - 1) :=
    Dvd.dvd.mul_right (Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) _) _
  unfold ordTwistedD
  rw [padicValNat_div_of_dvd hdvd (not_dvd_gcd_four hp5 _) hA, Nat.add_sub_cancel] at *
  rw [padicValNat.mul (mul_ne_zero (pow_ne_zero _ (by omega)) hr1) hprod0,
    padicValNat.mul (pow_ne_zero _ (by omega)) hr1,
    padicValNat.eq_zero_of_not_dvd (fun h => hpQ (hp.out.dvd_of_dvd_pow h)), zero_add,
    padicValNat.eq_zero_of_not_dvd (not_dvd_pow_add_one_of_odd hp5 heo hpe (r' + 1) (by omega)),
    zero_add, padicValNat_prod_sq_sub_one hp5 heo hpe hQ]

end Order

end CFSG.LocalAnalysis.RankFourTheoremC
