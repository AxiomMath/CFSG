module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

open CFSG.ComponentClassification.CatLeaf CFSG.Assembly.LowTwoRank

namespace OuterArith

theorem dvd_pow_sub_one {q i : ℕ} (h : 3 ∣ q - 1) : 3 ∣ q ^ i - 1 := by
  have := Nat.sub_dvd_pow_sub_pow q 1 i
  rw [one_pow] at this
  exact h.trans this

theorem dvd_sq_sub_one_of_add {q : ℕ} (h : 3 ∣ q + 1) : 3 ∣ q ^ 2 - 1 := by
  have e := Nat.pow_two_sub_pow_two q 1
  rw [one_pow] at e
  rw [e]
  exact Dvd.dvd.mul_right h _

theorem dvd_psu_factor {q i : ℕ} (h : 3 ∣ q + 1) :
    3 ∣ (if Even i then q ^ i - 1 else q ^ i + 1) := by
  by_cases he : Even i
  · rw [if_pos he]
    obtain ⟨m, hm⟩ := he
    have h2 := dvd_pow_sub_one (i := m) (dvd_sq_sub_one_of_add h)
    rwa [← pow_mul, show 2 * m = i by omega] at h2
  · rw [if_neg he]
    have h2 := Odd.nat_add_dvd_pow_add_pow q 1 (Nat.not_even_iff_odd.mp he)
    rw [one_pow] at h2
    exact h.trans h2

theorem dvd_sq_sub_one_of_not_dvd {q : ℕ} (h : ¬ 3 ∣ q) : 3 ∣ q ^ 2 - 1 := by
  have e := Nat.pow_two_sub_pow_two q 1
  rw [one_pow] at e
  rw [e]
  rcases (show q % 3 = 1 ∨ q % 3 = 2 by omega) with h1 | h2
  · exact Dvd.dvd.mul_left (by omega) _
  · exact Dvd.dvd.mul_right (by omega) _

theorem dvd_even_pow_sub_one {q i : ℕ} (h : ¬ 3 ∣ q) : 3 ∣ q ^ (2 * i) - 1 := by
  rw [pow_mul]
  exact dvd_pow_sub_one (dvd_sq_sub_one_of_not_dvd h)

theorem pow_dvd_pow_sub_one {x m : ℕ} (hx : 2 ≤ x) (hm : m ≠ 0) (h : 3 ∣ x - 1) :
    3 ^ (1 + m.factorization 3) ∣ x ^ m - 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnx : ¬ 3 ∣ x := by omega
  have hlte := padicValNat.pow_sub_pow (p := 3) (by decide) (by omega : 1 < x) h hnx hm
  rw [one_pow] at hlte
  have hne : x ^ m - 1 ≠ 0 := by
    have : 1 < x ^ m := Nat.one_lt_pow hm (by omega)
    omega
  have hv : 1 ≤ padicValNat 3 (x - 1) := one_le_padicValNat_of_dvd (by omega) h
  rw [Nat.factorization_def m Nat.prime_three]
  exact (padicValNat_dvd_iff_le hne).2 (by omega)

theorem pow_dvd_pow_add_one {x m : ℕ} (hm : Odd m) (h : 3 ∣ x + 1) :
    3 ^ (1 + m.factorization 3) ∣ x ^ m + 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnx : ¬ 3 ∣ x := by omega
  have hlte := padicValNat.pow_add_pow (p := 3) (by decide) h hnx hm
  rw [one_pow] at hlte
  have hv : 1 ≤ padicValNat 3 (x + 1) := one_le_padicValNat_of_dvd (by omega) h
  rw [Nat.factorization_def m Nat.prime_three]
  exact (padicValNat_dvd_iff_le (Nat.add_one_ne_zero _)).2 (by omega)

theorem pow_dvd_psu_factor {q n : ℕ} (hq : 2 ≤ q) (hn : n ≠ 0) (h : 3 ∣ q + 1) :
    3 ^ (1 + n.factorization 3) ∣ (if Even n then q ^ n - 1 else q ^ n + 1) := by
  by_cases he : Even n
  · rw [if_pos he]
    obtain ⟨m, hm⟩ := he
    have hm0 : m ≠ 0 := by omega
    have hn2 : n = 2 * m := by omega
    have h1 := pow_dvd_pow_sub_one (x := q ^ 2) (m := m) (by nlinarith) hm0
      (dvd_sq_sub_one_of_add h)
    have hfac : n.factorization 3 = m.factorization 3 := by
      rw [hn2, Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2), zero_add]
    rw [hfac, hn2, pow_mul]
    exact h1
  · rw [if_neg he]
    exact pow_dvd_pow_add_one (Nat.not_even_iff_odd.mp he) h

theorem pow_dvd_prod_Icc {n a : ℕ} {f : ℕ → ℕ} (hn : 5 ≤ n) (h2 : 3 ∣ f 2) (h3 : 3 ∣ f 3)
    (h4 : 3 ∣ f 4) (hf : 3 ^ a ∣ f n) : 3 ^ (3 + a) ∣ ∏ i ∈ Finset.Icc 2 n, f i := by
  have hsub : ({2, 3, 4, n} : Finset ℕ) ⊆ Finset.Icc 2 n := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_Icc]
    omega
  refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ f hsub)
  rw [Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
    Finset.prod_insert (by simp; omega), Finset.prod_singleton]
  have h := mul_dvd_mul h2 (mul_dvd_mul h3 (mul_dvd_mul h4 hf))
  have e : 3 ^ (3 + a) = 3 * (3 * (3 * 3 ^ a)) := by ring
  rw [e]
  exact h

theorem le_of_pow_dvd {N d M k j : ℕ} (hM : N * d = M) (hM0 : M ≠ 0) (hpow : 3 ^ k ∣ M)
    (hd : d.factorization 3 ≤ j) : k ≤ N.factorization 3 + j := by
  subst hM
  have hN0 : N ≠ 0 := left_ne_zero_of_mul hM0
  have hd0 : d ≠ 0 := right_ne_zero_of_mul hM0
  have h := (Nat.prime_three.pow_dvd_iff_le_factorization hM0).1 hpow
  rw [Nat.factorization_mul hN0 hd0, Finsupp.add_apply] at h
  omega

theorem factorization_eq_zero {d : ℕ} (h : ¬ 3 ∣ d) : d.factorization 3 = 0 :=
  Nat.factorization_eq_zero_of_not_dvd h

theorem factorization_gcd_le {n m : ℕ} (hn : n ≠ 0) :
    (Nat.gcd n m).factorization 3 ≤ n.factorization 3 :=
  (Nat.factorization_le_iff_dvd (Nat.gcd_ne_zero_left hn) hn).2 (Nat.gcd_dvd_left n m) 3

theorem psl_three_factorization {q N : ℕ} (hq : 2 ≤ q) (h : 3 ∣ q - 1)
    (hN : N * Nat.gcd 3 (q - 1) = lieOrderNumerator .PSL 3 q) :
    N.factorization 3 = 2 * padicValNat 3 (q - 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hg : Nat.gcd 3 (q - 1) = 3 := Nat.gcd_eq_left h
  rw [hg] at hN
  have hnum : lieOrderNumerator .PSL 3 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
    simp [lieOrderNumerator, Finset.prod_Icc_succ_top, show (3 : ℕ) * (3 - 1) / 2 = 3 from rfl]
  rw [hnum] at hN
  have hnq : ¬ 3 ∣ q := by omega
  have hq2 : q ^ 2 - 1 ≠ 0 := by have : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) hq; omega
  have hq3 : q ^ 3 - 1 ≠ 0 := by have : 1 < q ^ 3 := Nat.one_lt_pow (by norm_num) hq; omega
  have hq0 : q ^ 3 ≠ 0 := pow_ne_zero _ (by omega)
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp only [zero_mul] at hN
    exact (mul_ne_zero hq0 (mul_ne_zero hq2 hq3)) hN.symm
  have l2 := padicValNat.pow_sub_pow (p := 3) (by decide) (by omega : 1 < q) h hnq
    (n := 2) (by norm_num)
  have l3 := padicValNat.pow_sub_pow (p := 3) (by decide) (by omega : 1 < q) h hnq
    (n := 3) (by norm_num)
  rw [one_pow] at l2 l3
  have hv2 : padicValNat 3 2 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have hv3 : padicValNat 3 3 = 1 := padicValNat_self
  have hvq : padicValNat 3 (q ^ 3) = 0 := padicValNat.eq_zero_of_not_dvd
    (fun hd => hnq (Nat.prime_three.dvd_of_dvd_pow hd))
  have key := congrArg (padicValNat 3) hN
  rw [padicValNat.mul hN0 (by norm_num), padicValNat.mul hq0 (mul_ne_zero hq2 hq3),
    padicValNat.mul hq2 hq3, l2, l3, hv2, hv3, hvq] at key
  rw [Nat.factorization_def N Nat.prime_three]
  omega

theorem psu_three_factorization {q N : ℕ} (hq : 2 ≤ q) (h : 3 ∣ q + 1)
    (hN : N * Nat.gcd 3 (q + 1) = lieOrderNumerator .PSU 3 q) :
    N.factorization 3 = 2 * padicValNat 3 (q + 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hg : Nat.gcd 3 (q + 1) = 3 := Nat.gcd_eq_left h
  rw [hg] at hN
  have hnum : lieOrderNumerator .PSU 3 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
    simp [lieOrderNumerator, Finset.prod_Icc_succ_top, show (3 : ℕ) * (3 - 1) / 2 = 3 from rfl,
      show ¬ Even 3 from by decide]
  rw [hnum] at hN
  have hnq : ¬ 3 ∣ q := by omega
  have hq2 : q ^ 2 - 1 ≠ 0 := by have : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) hq; omega
  have hq0 : q ^ 3 ≠ 0 := pow_ne_zero _ (by omega)
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp only [zero_mul] at hN
    exact (mul_ne_zero hq0 (mul_ne_zero hq2 (Nat.add_one_ne_zero _))) hN.symm
  have l3 := padicValNat.pow_add_pow (p := 3) (by decide) h hnq (n := 3) (by decide)
  rw [one_pow] at l3
  have e2 : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    have := Nat.pow_two_sub_pow_two q 1
    rw [one_pow] at this
    exact this
  have hqm : q - 1 ≠ 0 := by omega
  have hvm : padicValNat 3 (q - 1) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
  have hv3 : padicValNat 3 3 = 1 := padicValNat_self
  have hvq : padicValNat 3 (q ^ 3) = 0 := padicValNat.eq_zero_of_not_dvd
    (fun hd => hnq (Nat.prime_three.dvd_of_dvd_pow hd))
  have key := congrArg (padicValNat 3) hN
  rw [padicValNat.mul hN0 (by norm_num), padicValNat.mul hq0 (mul_ne_zero hq2 (by omega)),
    padicValNat.mul hq2 (by omega), l3, e2, padicValNat.mul (by omega) hqm, hvm, hv3,
    hvq] at key
  rw [Nat.factorization_def N Nat.prime_three]
  omega

theorem psl_three_ne {q N : ℕ} (hq : 2 ≤ q) (h : 3 ∣ q - 1)
    (hN : N * Nat.gcd 3 (q - 1) = lieOrderNumerator .PSL 3 q) : N.factorization 3 ≠ 3 := by
  rw [psl_three_factorization hq h hN]
  omega

theorem psu_three_ne {q N : ℕ} (hq : 2 ≤ q) (h : 3 ∣ q + 1)
    (hN : N * Nat.gcd 3 (q + 1) = lieOrderNumerator .PSU 3 q) : N.factorization 3 ≠ 3 := by
  rw [psu_three_factorization hq h hN]
  omega

end OuterArith

open OuterArith

theorem three_lie_conditions {t : StatedLieTag} {n q N : ℕ} (hq : 2 ≤ q)
    (hN : N * lieOrderDivisor t n q = lieOrderNumerator t n q) (h3 : N.factorization 3 = 3) :
    ¬ 3 ∣ lieOrderDivisor t n q ∧ ¬ (t = .POmegaPlus ∧ n = 4) ∧ t ≠ .trialityD4 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq1 : 1 < q := hq
  refine ⟨fun hd => ?_, fun ⟨ht, hn⟩ => ?_, fun ht => ?_⟩
  · cases t
    ·
      have hpn : 3 ∣ n := (Nat.dvd_gcd_iff.mp hd).1
      have hpq : 3 ∣ q - 1 := (Nat.dvd_gcd_iff.mp hd).2
      rcases (show n = 0 ∨ n = 3 ∨ 6 ≤ n by omega) with rfl | rfl | hn6
      · have h1 : lieOrderNumerator .PSL 0 q = 1 := by simp [lieOrderNumerator]
        rw [h1] at hN
        have : lieOrderDivisor .PSL 0 q = 1 := Nat.eq_one_of_mul_eq_one_left hN
        rw [this] at hd
        omega
      · exact psl_three_ne hq hpq hN h3
      · have hn0 : n ≠ 0 := by omega
        have hprod := pow_dvd_prod_Icc (f := fun i => q ^ i - 1) (by omega : 5 ≤ n)
          (dvd_pow_sub_one hpq) (dvd_pow_sub_one hpq) (dvd_pow_sub_one hpq)
          (pow_dvd_pow_sub_one hq hn0 hpq)
        have hM : 3 ^ (3 + (1 + n.factorization 3)) ∣ lieOrderNumerator .PSL n q := by
          unfold lieOrderNumerator
          exact Dvd.dvd.mul_left hprod _
        have hM0 : lieOrderNumerator .PSL n q ≠ 0 := by
          unfold lieOrderNumerator
          refine mul_ne_zero (pow_ne_zero _ (by omega)) ?_
          rw [Finset.prod_ne_zero_iff]
          intro i hi
          rw [Finset.mem_Icc] at hi
          have : 1 < q ^ i := Nat.one_lt_pow (by omega) hq1
          omega
        have := le_of_pow_dvd hN hM0 hM (factorization_gcd_le hn0)
        omega
    ·
      have hpn : 3 ∣ n := (Nat.dvd_gcd_iff.mp hd).1
      have hpq : 3 ∣ q + 1 := (Nat.dvd_gcd_iff.mp hd).2
      rcases (show n = 0 ∨ n = 3 ∨ 6 ≤ n by omega) with rfl | rfl | hn6
      · have h1 : lieOrderNumerator .PSU 0 q = 1 := by simp [lieOrderNumerator]
        rw [h1] at hN
        have : lieOrderDivisor .PSU 0 q = 1 := Nat.eq_one_of_mul_eq_one_left hN
        rw [this] at hd
        omega
      · exact psu_three_ne hq hpq hN h3
      · have hn0 : n ≠ 0 := by omega
        have hprod := pow_dvd_prod_Icc (f := fun i => if Even i then q ^ i - 1 else q ^ i + 1)
          (by omega : 5 ≤ n) (dvd_psu_factor hpq) (dvd_psu_factor hpq) (dvd_psu_factor hpq)
          (pow_dvd_psu_factor hq hn0 hpq)
        have hM : 3 ^ (3 + (1 + n.factorization 3)) ∣ lieOrderNumerator .PSU n q := by
          unfold lieOrderNumerator
          exact Dvd.dvd.mul_left hprod _
        have hM0 : lieOrderNumerator .PSU n q ≠ 0 := by
          unfold lieOrderNumerator
          refine mul_ne_zero (pow_ne_zero _ (by omega)) ?_
          rw [Finset.prod_ne_zero_iff]
          intro i hi
          rw [Finset.mem_Icc] at hi
          have : 1 < q ^ i := Nat.one_lt_pow (by omega) hq1
          split_ifs <;> omega
        have := le_of_pow_dvd hN hM0 hM (factorization_gcd_le hn0)
        omega
    all_goals simp only [lieOrderDivisor] at hd
    ·
      exact absurd (Nat.le_of_dvd (by norm_num) (hd.trans (Nat.gcd_dvd_left _ _))) (by omega)
    ·
      omega
    ·
      exact absurd (hd.trans (Nat.gcd_dvd_left _ _)) (by norm_num)
    ·
      exact absurd (hd.trans (Nat.gcd_dvd_left _ _)) (by norm_num)
    ·
      omega
    ·
      omega
    ·
      have hpq : 3 ∣ q - 1 := (Nat.dvd_gcd_iff.mp hd).2
      have hM : 3 ^ 6 ∣ lieOrderNumerator .E6 n q := by
        unfold lieOrderNumerator
        have h := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul
          (dvd_pow_sub_one (i := 12) hpq) (dvd_pow_sub_one (i := 9) hpq))
          (dvd_pow_sub_one (i := 8) hpq)) (dvd_pow_sub_one (i := 6) hpq))
          (dvd_pow_sub_one (i := 5) hpq)) (dvd_pow_sub_one (i := 2) hpq)
        have e : 3 ^ 6 = 3 * 3 * 3 * 3 * 3 * 3 := by norm_num
        rw [e]
        simpa [mul_assoc] using Dvd.dvd.mul_left h (q ^ 36)
      have hM0 : lieOrderNumerator .E6 n q ≠ 0 := by
        unfold lieOrderNumerator
        have h1 : ∀ k, k ≠ 0 → q ^ k - 1 ≠ 0 := fun k hk => by
          have : 1 < q ^ k := Nat.one_lt_pow hk hq1
          omega
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
          (pow_ne_zero _ (by omega)) (h1 12 (by norm_num))) (h1 9 (by norm_num)))
          (h1 8 (by norm_num))) (h1 6 (by norm_num))) (h1 5 (by norm_num))) (h1 2 (by norm_num))
      have hdl : (lieOrderDivisor .E6 n q).factorization 3 ≤ 1 := by
        simp only [lieOrderDivisor]
        have hle := (Nat.factorization_le_iff_dvd (Nat.gcd_ne_zero_left (by norm_num))
          (by norm_num : (3 : ℕ) ≠ 0)).2 (Nat.gcd_dvd_left 3 (q - 1)) 3
        rw [Nat.Prime.factorization_self Nat.prime_three] at hle
        exact hle
      have := le_of_pow_dvd hN hM0 hM hdl
      omega
    ·
      exact absurd (Nat.le_of_dvd (by norm_num) (hd.trans (Nat.gcd_dvd_left _ _))) (by omega)
    ·
      omega
    ·
      have hpq : 3 ∣ q + 1 := (Nat.dvd_gcd_iff.mp hd).2
      have heven : ∀ k, 3 ∣ q ^ (2 * k) - 1 := fun k => by
        rw [pow_mul]; exact dvd_pow_sub_one (dvd_sq_sub_one_of_add hpq)
      have hodd : ∀ k, Odd k → 3 ∣ q ^ k + 1 := fun k hk => by
        have h2 := Odd.nat_add_dvd_pow_add_pow q 1 hk
        rw [one_pow] at h2
        exact hpq.trans h2
      have hM : 3 ^ 6 ∣ lieOrderNumerator .twistedE6 n q := by
        unfold lieOrderNumerator
        have h := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul
          (heven 6) (hodd 9 (by decide))) (heven 4)) (heven 3)) (hodd 5 (by decide))) (heven 1)
        have e : 3 ^ 6 = 3 * 3 * 3 * 3 * 3 * 3 := by norm_num
        rw [e]
        simpa [mul_assoc] using Dvd.dvd.mul_left h (q ^ 36)
      have hM0 : lieOrderNumerator .twistedE6 n q ≠ 0 := by
        unfold lieOrderNumerator
        have h1 : ∀ k, k ≠ 0 → q ^ k - 1 ≠ 0 := fun k hk => by
          have : 1 < q ^ k := Nat.one_lt_pow hk hq1
          omega
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
          (pow_ne_zero _ (by omega)) (h1 12 (by norm_num))) (Nat.add_one_ne_zero _))
          (h1 8 (by norm_num))) (h1 6 (by norm_num))) (Nat.add_one_ne_zero _)) (h1 2 (by norm_num))
      have hdl : (lieOrderDivisor .twistedE6 n q).factorization 3 ≤ 1 := by
        simp only [lieOrderDivisor]
        have hle := (Nat.factorization_le_iff_dvd (Nat.gcd_ne_zero_left (by norm_num))
          (by norm_num : (3 : ℕ) ≠ 0)).2 (Nat.gcd_dvd_left 3 (q + 1)) 3
        rw [Nat.Prime.factorization_self Nat.prime_three] at hle
        exact hle
      have := le_of_pow_dvd hN hM0 hM hdl
      omega
    all_goals omega
  ·
    subst ht hn
    have hM : 3 ^ 4 ∣ lieOrderNumerator .POmegaPlus 4 q := by
      unfold lieOrderNumerator
      by_cases h3q : 3 ∣ q
      · refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
        exact (pow_dvd_pow_of_dvd h3q 4).trans (pow_dvd_pow q (by norm_num))
      · have hP : 3 ^ 3 ∣ ∏ i ∈ Finset.Icc 1 (4 - 1), (q ^ (2 * i) - 1) := by
          simp only [show (4 : ℕ) - 1 = 3 from rfl, Finset.prod_Icc_succ_top
            (show 1 ≤ 3 by norm_num), Finset.prod_Icc_succ_top (show 1 ≤ 2 by norm_num),
            Finset.Icc_self, Finset.prod_singleton]
          have h := mul_dvd_mul (mul_dvd_mul (dvd_even_pow_sub_one (i := 1) h3q)
            (dvd_even_pow_sub_one (i := 2) h3q)) (dvd_even_pow_sub_one (i := 3) h3q)
          simpa [pow_succ] using h
        have h4 : 3 ∣ q ^ 4 - 1 := by
          have := dvd_even_pow_sub_one (i := 2) h3q
          simpa using this
        have := mul_dvd_mul (Dvd.dvd.mul_left h4 (q ^ (4 * (4 - 1)))) hP
        simpa [pow_succ, mul_assoc] using this
    have hM0 : lieOrderNumerator .POmegaPlus 4 q ≠ 0 := by
      unfold lieOrderNumerator
      refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by omega)) ?_) ?_
      · have : 1 < q ^ 4 := Nat.one_lt_pow (by norm_num) hq1
        omega
      · rw [Finset.prod_ne_zero_iff]
        intro i hi
        rw [Finset.mem_Icc] at hi
        have : 1 < q ^ (2 * i) := Nat.one_lt_pow (by omega) hq1
        omega
    have hd0 : (lieOrderDivisor .POmegaPlus 4 q).factorization 3 ≤ 0 := by
      simp only [lieOrderDivisor]
      rw [factorization_eq_zero (fun h => absurd (h.trans (Nat.gcd_dvd_left 4 _)) (by norm_num))]
    have := le_of_pow_dvd hN hM0 hM hd0
    omega
  ·
    subst ht
    have hM : 3 ^ 4 ∣ lieOrderNumerator .trialityD4 n q := by
      unfold lieOrderNumerator
      by_cases h3q : 3 ∣ q
      · refine Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _) _
        exact (pow_dvd_pow_of_dvd h3q 4).trans (pow_dvd_pow q (by norm_num))
      · have h2 : 3 ∣ q ^ 2 - 1 := dvd_sq_sub_one_of_not_dvd h3q
        have h6 : 3 ^ 2 ∣ q ^ 6 - 1 := by
          have := pow_dvd_pow_sub_one (x := q ^ 2) (m := 3) (by nlinarith) (by norm_num) h2
          rw [← pow_mul] at this
          have hf : (3 : ℕ).factorization 3 = 1 := Nat.Prime.factorization_self Nat.prime_three
          rw [hf] at this
          simpa using this
        have h8 : 3 ∣ q ^ 8 + q ^ 4 + 1 := by
          rcases (show q % 3 = 1 ∨ q % 3 = 2 by omega) with h | h <;>
          · apply Nat.dvd_of_mod_eq_zero
            simp [Nat.add_mod, Nat.pow_mod, h]
        have := mul_dvd_mul (mul_dvd_mul (Dvd.dvd.mul_left h8 (q ^ 12)) h6) h2
        have e : 3 ^ 4 = 3 * 3 ^ 2 * 3 := by norm_num
        rw [e]
        simpa [mul_assoc] using this
    have hM0 : lieOrderNumerator .trialityD4 n q ≠ 0 := by
      unfold lieOrderNumerator
      have h1 : ∀ k, k ≠ 0 → q ^ k - 1 ≠ 0 := fun k hk => by
        have : 1 < q ^ k := Nat.one_lt_pow hk hq1
        omega
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by omega))
        (Nat.add_one_ne_zero _)) (h1 6 (by norm_num))) (h1 2 (by norm_num))
    have hd0 : (lieOrderDivisor .trialityD4 n q).factorization 3 ≤ 0 := by
      simp [lieOrderDivisor]
    have := le_of_pow_dvd hN hM0 hM hd0
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree
