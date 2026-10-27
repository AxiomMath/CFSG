module

public import CFSG.Open.Defs
public import CFSG.LocalAnalysis.ComponentClassification.LieOrderTwoAdic

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.ComponentClassification.CatLeafProof CFSG.RankThree.PartTwo.KFacts.OddChar

namespace OrderTwoPart

variable {q : ℕ}

theorem fac_two_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).factorization 2 = a.factorization 2 + b.factorization 2 := by
  rw [Nat.factorization_mul ha hb, Finsupp.add_apply]

theorem fac_two_of_mul_eq (hq : Odd q) {N g e x : ℕ} (hg : g ≠ 0) (hx : x ≠ 0)
    (h : N * g = q ^ e * x) : N.factorization 2 + g.factorization 2 = x.factorization 2 := by
  have hq0 : q ^ e ≠ 0 := pow_ne_zero _ hq.pos.ne'
  have hN : N ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h
    exact mul_ne_zero hq0 hx h.symm
  rw [← fac_two_mul hN hg, h, fac_two_mul hq0 hx, Nat.factorization_pow, Finsupp.smul_apply,
    Nat.factorization_eq_zero_of_not_dvd hq.not_two_dvd_nat, smul_zero, zero_add]

theorem fac_two_gcd {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Nat.gcd a b).factorization 2 = min (a.factorization 2) (b.factorization 2) := by
  have h := congrArg (· 2) (Nat.factorization_gcd ha hb)
  simpa using h

theorem fac_two_gcd_of_odd {k : ℕ} (hk : Odd k) (x : ℕ) : (Nat.gcd k x).factorization 2 = 0 :=
  Nat.factorization_eq_zero_of_not_dvd fun h => hk.not_two_dvd_nat (h.trans (Nat.gcd_dvd_left k x))

theorem fac_two_six : (6 : ℕ).factorization 2 = 1 := by
  rw [Nat.factorization_def _ Nat.prime_two]
  exact padicValNat_eq_one_of_mod_four (by norm_num)

theorem fac_two_sq_sub_one (hq : Odd q) (hq1 : 1 < q) :
    (q ^ 2 - 1).factorization 2 = (q - 1).factorization 2 + (q + 1).factorization 2 := by
  simp only [Nat.factorization_def _ Nat.prime_two]
  exact padicValNat_sq_sub_one hq hq1

theorem fac_two_pow_sub_one_of_odd (hq : Odd q) (hq1 : 1 < q) {j : ℕ} (hj : Odd j) :
    (q ^ j - 1).factorization 2 = (q - 1).factorization 2 := by
  simp only [Nat.factorization_def _ Nat.prime_two]
  exact padicValNat_pow_sub_one_of_odd hq hq1 hj

theorem fac_two_pow_add_one_of_odd (hq : Odd q) {j : ℕ} (hj : Odd j) :
    (q ^ j + 1).factorization 2 = (q + 1).factorization 2 := by
  simp only [Nat.factorization_def _ Nat.prime_two]
  exact padicValNat_pow_add_one_of_odd hq hj

theorem fac_two_pow_four_sub_one (hq : Odd q) (hq1 : 1 < q) :
    (q ^ 4 - 1).factorization 2 = (q ^ 2 - 1).factorization 2 + 1 := by
  simp only [Nat.factorization_def _ Nat.prime_two]
  exact padicValNat_pow_four_sub_one hq hq1

theorem fac_two_pow_six_sub_one (hq : Odd q) (hq1 : 1 < q) :
    (q ^ 6 - 1).factorization 2 = (q ^ 2 - 1).factorization 2 := by
  simp only [Nat.factorization_def _ Nat.prime_two]
  exact padicValNat_pow_six_sub_one hq hq1

theorem fac_two_sub_one_of_three (hq : q % 4 = 3) : (q - 1).factorization 2 = 1 := by
  rw [Nat.factorization_def _ Nat.prime_two]
  exact padicValNat_eq_one_of_mod_four (by omega)

theorem fac_two_add_one_of_one (hq : q % 4 = 1) : (q + 1).factorization 2 = 1 := by
  rw [Nat.factorization_def _ Nat.prime_two]
  exact padicValNat_eq_one_of_mod_four (by omega)

theorem one_le_fac_two_add_one (hq : Odd q) : 1 ≤ (q + 1).factorization 2 :=
  (Nat.prime_two.dvd_iff_one_le_factorization (by omega)).mp (by
    have := Nat.odd_iff.mp hq
    omega)

theorem pow_sub_one_ne_zero_of_two_le (hq1 : 1 < q) {i : ℕ} (hi : 2 ≤ i) : q ^ i - 1 ≠ 0 := by
  have : 1 < q ^ i := Nat.one_lt_pow (by omega) hq1
  omega

theorem twisted_factor_of_even (hq : 1 ≤ q) {i : ℕ} (hi : Even i) :
    ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat = q ^ i - 1 := by
  rw [hi.neg_one_pow]
  have : 1 ≤ q ^ i := Nat.one_le_pow _ _ hq
  have h : ((q : ℤ) ^ i - 1) = ((q ^ i - 1 : ℕ) : ℤ) := by push_cast [this]; ring
  rw [h, Int.toNat_natCast]

theorem twisted_factor_of_odd {i : ℕ} (hi : Odd i) :
    ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat = q ^ i + 1 := by
  rw [hi.neg_one_pow, sub_neg_eq_add]
  have h : ((q : ℤ) ^ i + 1) = ((q ^ i + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

theorem twisted_factor_ne_zero (hq1 : 1 < q) {i : ℕ} (hi : 2 ≤ i) :
    ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat ≠ 0 := by
  rcases Nat.even_or_odd i with he | ho
  · rw [twisted_factor_of_even hq1.le he]
    exact pow_sub_one_ne_zero_of_two_le hq1 hi
  · rw [twisted_factor_of_odd ho]
    omega

theorem ordA_mul_gcd {n : ℕ} (hn : 1 ≤ n) :
    Open.ordA n q * Nat.gcd (n + 1) (q - 1) =
      q ^ (n * (n + 1) / 2) * ∏ i ∈ Finset.Icc 2 (n + 1), (q ^ i - 1) := by
  rw [Open.ordA]
  refine Nat.div_mul_cancel ((Nat.gcd_dvd_right _ _).trans (Dvd.dvd.mul_left ?_ _))
  have h2 : q - 1 ∣ q ^ 2 - 1 := by simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow q 1 2
  exact h2.trans (Finset.dvd_prod_of_mem (fun i => q ^ i - 1)
    (Finset.mem_Icc.mpr ⟨le_rfl, (by omega : 2 ≤ n + 1)⟩))

theorem fac_two_ordA_add {n : ℕ} (hn : 1 ≤ n) (hq : Odd q) (hq1 : 1 < q) :
    (Open.ordA n q).factorization 2 + (Nat.gcd (n + 1) (q - 1)).factorization 2 =
      ∑ i ∈ Finset.Icc 2 (n + 1), (q ^ i - 1).factorization 2 := by
  have hP : ∀ i ∈ Finset.Icc 2 (n + 1), q ^ i - 1 ≠ 0 := fun i hi =>
    pow_sub_one_ne_zero_of_two_le hq1 (Finset.mem_Icc.mp hi).1
  have h := fac_two_of_mul_eq hq (Nat.gcd_ne_zero_left (by omega))
    (Finset.prod_ne_zero_iff.mpr hP) (ordA_mul_gcd hn)
  rwa [Nat.factorization_prod_apply hP] at h

theorem ordTwistedA_mul_gcd {n : ℕ} (hn : 1 ≤ n) (hq1 : 1 ≤ q) :
    Open.ordTwistedA n q * Nat.gcd (n + 1) (q + 1) =
      q ^ (n * (n + 1) / 2) *
        ∏ i ∈ Finset.Icc 2 (n + 1), ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat := by
  rw [Open.ordTwistedA]
  refine Nat.div_mul_cancel ((Nat.gcd_dvd_right _ _).trans (Dvd.dvd.mul_left ?_ _))
  have h2 : q + 1 ∣ ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat := by
    rw [twisted_factor_of_even hq1 even_two]
    exact ⟨q - 1, by
      have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
      zify [this, hq1]
      ring⟩
  exact h2.trans (Finset.dvd_prod_of_mem (fun i => ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat)
    (Finset.mem_Icc.mpr ⟨le_rfl, (by omega : 2 ≤ n + 1)⟩))

theorem fac_two_ordTwistedA_add {n : ℕ} (hn : 1 ≤ n) (hq : Odd q) (hq1 : 1 < q) :
    (Open.ordTwistedA n q).factorization 2 + (Nat.gcd (n + 1) (q + 1)).factorization 2 =
      ∑ i ∈ Finset.Icc 2 (n + 1), (((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat).factorization 2 := by
  have hP : ∀ i ∈ Finset.Icc 2 (n + 1), ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat ≠ 0 := fun i hi =>
    twisted_factor_ne_zero hq1 (Finset.mem_Icc.mp hi).1
  have h := fac_two_of_mul_eq hq (Nat.gcd_ne_zero_left (by omega))
    (Finset.prod_ne_zero_iff.mpr hP) (ordTwistedA_mul_gcd hn hq1.le)
  rwa [Nat.factorization_prod_apply hP] at h

theorem ordBC_mul_gcd {n : ℕ} (hn : 1 ≤ n) :
    Open.ordBC n q * Nat.gcd 2 (q - 1) =
      q ^ (n * n) * ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) := by
  rw [Open.ordBC]
  refine Nat.div_mul_cancel ((Nat.gcd_dvd_right _ _).trans (Dvd.dvd.mul_left ?_ _))
  have h2 : q - 1 ∣ q ^ (2 * 1) - 1 := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow q 1 (2 * 1)
  exact h2.trans (Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1)
    (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩))

theorem fac_two_ordBC_add {n : ℕ} (hn : 1 ≤ n) (hq : Odd q) (hq1 : 1 < q) :
    (Open.ordBC n q).factorization 2 + (Nat.gcd 2 (q - 1)).factorization 2 =
      ∑ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1).factorization 2 := by
  have hP : ∀ i ∈ Finset.Icc 1 n, q ^ (2 * i) - 1 ≠ 0 := fun i hi =>
    pow_sub_one_ne_zero_of_two_le hq1 (by have := (Finset.mem_Icc.mp hi).1; omega)
  have h := fac_two_of_mul_eq hq (Nat.gcd_ne_zero_left (by omega))
    (Finset.prod_ne_zero_iff.mpr hP) (ordBC_mul_gcd hn)
  rwa [Nat.factorization_prod_apply hP] at h

theorem fac_two_gcd_two_sub_one (hq : Odd q) : (Nat.gcd 2 (q - 1)).factorization 2 = 1 := by
  rw [Nat.gcd_eq_left (by have := Nat.odd_iff.mp hq; omega), Nat.prime_two.factorization_self]

end OrderTwoPart

open OrderTwoPart

variable {q : ℕ}

theorem factorization_two_ordA_three_of_three (hq4 : q % 4 = 3) :
    (Open.ordA 3 q).factorization 2 = 2 * (q ^ 2 - 1).factorization 2 + 1 := by
  have hq : Odd q := Nat.odd_iff.mpr (by omega)
  have hq1 : 1 < q := by omega
  have h := fac_two_ordA_add (n := 3) (by norm_num) hq hq1
  have hg : Nat.gcd (3 + 1) (q - 1) = 2 := by
    rw [Nat.gcd_rec, show (q - 1) % (3 + 1) = 2 by omega]
    rfl
  rw [hg, Nat.prime_two.factorization_self, show (3 : ℕ) + 1 = 4 from rfl,
    show Finset.Icc 2 4 = {2, 3, 4} from rfl, Finset.sum_insert (by decide),
    Finset.sum_pair (by norm_num), fac_two_pow_sub_one_of_odd hq hq1 (by decide : Odd 3),
    fac_two_pow_four_sub_one hq hq1, fac_two_sub_one_of_three hq4] at h
  omega

theorem factorization_two_ordTwistedA_three_of_one (hq4 : q % 4 = 1) (hq1 : 1 < q) :
    (Open.ordTwistedA 3 q).factorization 2 = 2 * (q ^ 2 - 1).factorization 2 + 1 := by
  have hq : Odd q := Nat.odd_iff.mpr (by omega)
  have h := fac_two_ordTwistedA_add (n := 3) (by norm_num) hq hq1
  have hg : Nat.gcd (3 + 1) (q + 1) = 2 := by
    rw [Nat.gcd_rec, show (q + 1) % (3 + 1) = 2 by omega]
    rfl
  rw [hg, Nat.prime_two.factorization_self, show (3 : ℕ) + 1 = 4 from rfl,
    show Finset.Icc 2 4 = {2, 3, 4} from rfl, Finset.sum_insert (by decide),
    Finset.sum_pair (by norm_num), twisted_factor_of_even hq1.le even_two,
    twisted_factor_of_odd (by decide : Odd 3), twisted_factor_of_even hq1.le (by decide : Even 4),
    fac_two_pow_add_one_of_odd hq (by decide : Odd 3), fac_two_pow_four_sub_one hq hq1,
    fac_two_add_one_of_one hq4] at h
  omega

theorem factorization_two_ordA_four_of_three (hq4 : q % 4 = 3) :
    (Open.ordA 4 q).factorization 2 = 2 * (q ^ 2 - 1).factorization 2 + 3 := by
  have hq : Odd q := Nat.odd_iff.mpr (by omega)
  have hq1 : 1 < q := by omega
  have h := fac_two_ordA_add (n := 4) (by norm_num) hq hq1
  rw [show (4 : ℕ) + 1 = 5 from rfl, fac_two_gcd_of_odd (by decide : Odd 5),
    show Finset.Icc 2 5 = {2, 3, 4, 5} from rfl, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_pair (by norm_num),
    fac_two_pow_sub_one_of_odd hq hq1 (by decide : Odd 3),
    fac_two_pow_sub_one_of_odd hq hq1 (by decide : Odd 5),
    fac_two_pow_four_sub_one hq hq1, fac_two_sub_one_of_three hq4] at h
  omega

theorem factorization_two_ordTwistedA_four_of_one (hq4 : q % 4 = 1) (hq1 : 1 < q) :
    (Open.ordTwistedA 4 q).factorization 2 = 2 * (q ^ 2 - 1).factorization 2 + 3 := by
  have hq : Odd q := Nat.odd_iff.mpr (by omega)
  have h := fac_two_ordTwistedA_add (n := 4) (by norm_num) hq hq1
  rw [show (4 : ℕ) + 1 = 5 from rfl, fac_two_gcd_of_odd (by decide : Odd 5),
    show Finset.Icc 2 5 = {2, 3, 4, 5} from rfl, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_pair (by norm_num),
    twisted_factor_of_even hq1.le even_two, twisted_factor_of_odd (by decide : Odd 3),
    twisted_factor_of_even hq1.le (by decide : Even 4), twisted_factor_of_odd (by decide : Odd 5),
    fac_two_pow_add_one_of_odd hq (by decide : Odd 3),
    fac_two_pow_add_one_of_odd hq (by decide : Odd 5), fac_two_pow_four_sub_one hq hq1,
    fac_two_add_one_of_one hq4] at h
  omega

theorem factorization_two_ordA_five_of_three (hq4 : q % 4 = 3) :
    (Open.ordA 5 q).factorization 2 = 3 * (q ^ 2 - 1).factorization 2 + 2 := by
  have hq : Odd q := Nat.odd_iff.mpr (by omega)
  have hq1 : 1 < q := by omega
  have h := fac_two_ordA_add (n := 5) (by norm_num) hq hq1
  have hg : (Nat.gcd (5 + 1) (q - 1)).factorization 2 = 1 := by
    rw [fac_two_gcd (by norm_num) (by omega), show (5 : ℕ) + 1 = 6 from rfl, fac_two_six,
      fac_two_sub_one_of_three hq4, min_self]
  rw [hg, show (5 : ℕ) + 1 = 6 from rfl,
    show Finset.Icc 2 6 = {2, 3, 4, 5, 6} from rfl, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_pair (by norm_num),
    fac_two_pow_sub_one_of_odd hq hq1 (by decide : Odd 3),
    fac_two_pow_sub_one_of_odd hq hq1 (by decide : Odd 5),
    fac_two_pow_four_sub_one hq hq1, fac_two_pow_six_sub_one hq hq1,
    fac_two_sub_one_of_three hq4] at h
  omega

theorem factorization_two_ordTwistedA_five_of_one (hq4 : q % 4 = 1) (hq1 : 1 < q) :
    (Open.ordTwistedA 5 q).factorization 2 = 3 * (q ^ 2 - 1).factorization 2 + 2 := by
  have hq : Odd q := Nat.odd_iff.mpr (by omega)
  have h := fac_two_ordTwistedA_add (n := 5) (by norm_num) hq hq1
  have hg : (Nat.gcd (5 + 1) (q + 1)).factorization 2 = 1 := by
    rw [fac_two_gcd (by norm_num) (by omega), show (5 : ℕ) + 1 = 6 from rfl, fac_two_six,
      fac_two_add_one_of_one hq4, min_self]
  rw [hg, show (5 : ℕ) + 1 = 6 from rfl,
    show Finset.Icc 2 6 = {2, 3, 4, 5, 6} from rfl, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_pair (by norm_num),
    twisted_factor_of_even hq1.le even_two, twisted_factor_of_odd (by decide : Odd 3),
    twisted_factor_of_even hq1.le (by decide : Even 4), twisted_factor_of_odd (by decide : Odd 5),
    twisted_factor_of_even hq1.le (by decide : Even 6),
    fac_two_pow_add_one_of_odd hq (by decide : Odd 3),
    fac_two_pow_add_one_of_odd hq (by decide : Odd 5), fac_two_pow_four_sub_one hq hq1,
    fac_two_pow_six_sub_one hq hq1, fac_two_add_one_of_one hq4] at h
  omega

theorem factorization_two_ordBC_two (hq : Odd q) (hq3 : 3 ≤ q) :
    (Open.ordBC 2 q).factorization 2 = 2 * (q ^ 2 - 1).factorization 2 := by
  have hq1 : 1 < q := by omega
  have h := fac_two_ordBC_add (n := 2) (by norm_num) hq hq1
  rw [fac_two_gcd_two_sub_one hq, show Finset.Icc 1 2 = {1, 2} from rfl,
    Finset.sum_pair (by norm_num), show 2 * 1 = 2 from rfl, show 2 * 2 = 4 from rfl,
    fac_two_pow_four_sub_one hq hq1] at h
  omega

theorem factorization_two_ordBC_three (hq : Odd q) (hq3 : 3 ≤ q) :
    (Open.ordBC 3 q).factorization 2 = 3 * (q ^ 2 - 1).factorization 2 := by
  have hq1 : 1 < q := by omega
  have h := fac_two_ordBC_add (n := 3) (by norm_num) hq hq1
  rw [fac_two_gcd_two_sub_one hq, show Finset.Icc 1 3 = {1, 2, 3} from rfl,
    Finset.sum_insert (by decide), Finset.sum_pair (by norm_num), show 2 * 1 = 2 from rfl,
    show 2 * 2 = 4 from rfl, show 2 * 3 = 6 from rfl, fac_two_pow_four_sub_one hq hq1,
    fac_two_pow_six_sub_one hq hq1] at h
  omega

theorem factorization_two_ordRee {f : ℕ} (hf : Odd f) :
    (Open.ordRee (3 ^ f)).factorization 2 = 3 := by
  have hq : Odd (3 ^ f) := Odd.pow (by decide)
  have hq1 : 1 < 3 ^ f := Nat.one_lt_pow hf.pos.ne' (by norm_num)
  have h3 : (3 ^ f) ^ 3 + 1 ≠ 0 := by omega
  have h1 : 3 ^ f - 1 ≠ 0 := by omega
  have h := fac_two_of_mul_eq hq (N := Open.ordRee (3 ^ f)) (g := 1) (e := 3) one_ne_zero
    (mul_ne_zero h3 h1) (by rw [Open.ordRee, mul_one, mul_assoc])
  rw [Nat.factorization_one, Finsupp.zero_apply, add_zero, fac_two_mul h3 h1,
    fac_two_pow_add_one_of_odd hq (by decide : Odd 3),
    Nat.factorization_def (3 ^ f + 1) Nat.prime_two, Nat.factorization_def (3 ^ f - 1) Nat.prime_two,
    padicValNat_three_pow_add_one_of_odd hf, padicValNat_three_pow_sub_one_of_odd hf] at h
  omega

end CFSG.LocalAnalysis.Mason73
