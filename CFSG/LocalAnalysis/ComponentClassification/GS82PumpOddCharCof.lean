module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpOddCharLTE
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrderArith

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.OddChar

open Finset CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof

theorem fac_natCast {q : ℕ} (hq : 1 ≤ q) (d : ℕ) : fac (q : ℤ) d = q ^ d - 1 := by
  have h1 : 1 ≤ q ^ d := Nat.one_le_pow _ _ hq
  rw [fac, show (q : ℤ) ^ d - 1 = ((q ^ d - 1 : ℕ) : ℤ) by
    rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one], Int.natAbs_natCast]

theorem fac_neg_of_even {q d : ℕ} (hq : 1 ≤ q) (hd : Even d) : fac (-(q : ℤ)) d = q ^ d - 1 := by
  show ((-(q : ℤ)) ^ d - 1).natAbs = _
  rw [hd.neg_pow]
  exact fac_natCast hq d

theorem fac_neg_of_odd {q d : ℕ} (hd : Odd d) : fac (-(q : ℤ)) d = q ^ d + 1 := by
  show ((-(q : ℤ)) ^ d - 1).natAbs = _
  rw [hd.neg_pow, show -(q : ℤ) ^ d - 1 = -((q ^ d + 1 : ℕ) : ℤ) by push_cast; ring,
    Int.natAbs_neg, Int.natAbs_natCast]

theorem fac_neg {q : ℕ} (hq : 1 ≤ q) (d : ℕ) :
    fac (-(q : ℤ)) d = if Even d then q ^ d - 1 else q ^ d + 1 := by
  split_ifs with hd
  · exact fac_neg_of_even hq hd
  · exact fac_neg_of_odd (Nat.not_even_iff_odd.mp hd)

theorem setup_of {p f s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hs : s.Prime)
    (hs2 : s ≠ 2) (hsp : s ≠ p) {Q : ℤ} (hQ : Q.natAbs = p ^ f) : Setup s (p ^ f) Q where
  prime := hs
  odd_s := hs.odd_of_ne_two hs2
  natAbs_eq := hQ
  three_le := by
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    exact h3.trans (Nat.le_self_pow (by omega) p)
  odd_q := (hp.odd_of_ne_two hp2).pow
  not_dvd := fun hdvd => hsp ((Nat.prime_dvd_prime_iff_eq hs hp).mp (hs.dvd_of_dvd_pow hdvd))

namespace Setup

variable {s q : ℕ} {Q : ℤ}

theorem one_le (h : Setup s q Q) : 1 ≤ q := by
  have := h.three_le
  omega

theorem ordProj_prod_fac_le (h : Setup s q Q) {D : Finset ℕ} (hD : ∀ d ∈ D, 2 ≤ d)
    (h2 : 2 ∈ D) : ordProj[s] (∏ d ∈ D, fac Q d) ≤ q ^ ∑ d ∈ D, (d - 1) := by
  rw [ordProj_prod fun d hd => h.fac_ne_zero (by have := hD d hd; omega)]
  exact h.prod_ordProj_fac_le (deg := fun d => d) hD h2 rfl fun i _ j _ hij _ => hij

theorem le_of_eq_prod (h : Setup s q Q) {D : Finset ℕ} (hD : ∀ d ∈ D, 2 ≤ d) (h2 : 2 ∈ D)
    {C N : ℕ} (hC : C = ∏ d ∈ D, fac Q d) (hN : ∑ d ∈ D, (d - 1) = N) :
    ordProj[s] C ≤ q ^ N := by
  rw [hC, ← hN]
  exact h.ordProj_prod_fac_le hD h2

theorem ordProj_prod_fac_even_le (h : Setup s q Q) {m : ℕ} (hm : 1 ≤ m) :
    ordProj[s] (∏ i ∈ Icc 1 m, fac Q (2 * i)) ≤ q ^ ∑ i ∈ Icc 1 m, (2 * i - 1) := by
  have hmem : ∀ i ∈ Icc 1 m, 1 ≤ i := fun i hi => (Finset.mem_Icc.mp hi).1
  rw [ordProj_prod fun i hi => h.fac_ne_zero (by have := hmem i hi; omega)]
  refine h.prod_ordProj_fac_le (deg := fun i => 2 * i) (fun i hi => by have := hmem i hi; omega)
    (Finset.mem_Icc.mpr ⟨le_rfl, hm⟩) rfl fun i _ j _ _ hodd => ?_
  exact absurd hodd (Nat.not_odd_iff_even.mpr (even_two_mul i))

end Setup

theorem two_mul_sum_Icc_two_sub_one (n : ℕ) : 2 * ∑ i ∈ Icc 2 n, (i - 1) = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring

theorem sum_Icc_two_sub_one (n : ℕ) : ∑ i ∈ Icc 2 n, (i - 1) = n * (n - 1) / 2 := by
  rw [← two_mul_sum_Icc_two_sub_one n, Nat.mul_div_cancel_left _ two_pos]

theorem sum_Icc_one_two_mul_sub_one (n : ℕ) : ∑ i ∈ Icc 1 n, (2 * i - 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
    ring

theorem sub_one_add_sq_sub_one {n : ℕ} (hn : 1 ≤ n) : n - 1 + (n - 1) ^ 2 = n * (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

namespace Setup

variable {s q : ℕ} {Q : ℤ}

theorem ordProj_cof_PSL (h : Setup s q q) {n : ℕ} (hn : 2 ≤ n) :
    ordProj[s] (∏ i ∈ Icc 2 n, (q ^ i - 1)) ≤ q ^ (n * (n - 1) / 2) := by
  rw [← sum_Icc_two_sub_one, ← Finset.prod_congr rfl fun i _ => fac_natCast h.one_le i]
  exact h.ordProj_prod_fac_le (fun d hd => (Finset.mem_Icc.mp hd).1)
    (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)

theorem ordProj_cof_PSU (h : Setup s q (-(q : ℤ))) {n : ℕ} (hn : 2 ≤ n) :
    ordProj[s] (∏ i ∈ Icc 2 n, (if Even i then q ^ i - 1 else q ^ i + 1)) ≤
      q ^ (n * (n - 1) / 2) := by
  rw [← sum_Icc_two_sub_one, ← Finset.prod_congr rfl fun i _ => fac_neg h.one_le i]
  exact h.ordProj_prod_fac_le (fun d hd => (Finset.mem_Icc.mp hd).1)
    (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)

theorem ordProj_cof_PSp (h : Setup s q q) {n : ℕ} (hn : 1 ≤ n) :
    ordProj[s] (∏ i ∈ Icc 1 n, (q ^ (2 * i) - 1)) ≤ q ^ (n ^ 2) := by
  rw [← sum_Icc_one_two_mul_sub_one, ← Finset.prod_congr rfl fun i _ => fac_natCast h.one_le _]
  exact h.ordProj_prod_fac_even_le hn

theorem ordProj_cof_orth (h : Setup s q Q) {n : ℕ} (hn : 2 ≤ n) :
    ordProj[s] (fac Q n * ∏ i ∈ Icc 1 (n - 1), fac Q (2 * i)) ≤ q ^ (n * (n - 1)) := by
  have h0 : (0 : ℕ) ∉ Icc 1 (n - 1) := by simp
  have hmem : ∀ i ∈ Icc 1 (n - 1), 1 ≤ i := fun i hi => (Finset.mem_Icc.mp hi).1
  let deg : ℕ → ℕ := fun i => if i = 0 then n else 2 * i
  have hdeg : ∀ i ∈ insert 0 (Icc 1 (n - 1)), 2 ≤ deg i := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · simpa [deg] using hn
    · have := hmem i hi
      simp only [deg, if_neg (show i ≠ 0 by omega)]
      omega
  have hprod : fac Q n * ∏ i ∈ Icc 1 (n - 1), fac Q (2 * i) =
      ∏ i ∈ insert 0 (Icc 1 (n - 1)), fac Q (deg i) := by
    rw [Finset.prod_insert h0]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    have := hmem i hi
    simp only [deg, if_neg (show i ≠ 0 by omega)]
  have hsum : ∑ i ∈ insert 0 (Icc 1 (n - 1)), (deg i - 1) = n * (n - 1) := by
    rw [Finset.sum_insert h0, ← sub_one_add_sq_sub_one (by omega : 1 ≤ n),
      ← sum_Icc_one_two_mul_sub_one]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have := hmem i hi
    simp only [deg, if_neg (show i ≠ 0 by omega)]
  have hzero : ∀ i ∈ insert 0 (Icc 1 (n - 1)), Odd (deg i) → i = 0 := by
    intro i _ hodd
    by_contra hi
    simp only [deg, if_neg hi] at hodd
    exact Nat.not_odd_iff_even.mpr (even_two_mul i) hodd
  rw [hprod, ← hsum, ordProj_prod fun i hi => h.fac_ne_zero (by have := hdeg i hi; omega)]
  refine h.prod_ordProj_fac_le hdeg (i₂ := 1) (Finset.mem_insert_of_mem
    (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)) rfl fun i hi j hj hij hodd => ?_
  rw [hzero i hi hodd, hzero j hj (hij ▸ hodd)]

theorem ordProj_cof_orthPlus (h : Setup s q q) {n : ℕ} (hn : 2 ≤ n) :
    ordProj[s] ((q ^ n - 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) ≤ q ^ (n * (n - 1)) := by
  rw [← fac_natCast h.one_le, ← Finset.prod_congr rfl fun i _ => fac_natCast h.one_le _]
  exact h.ordProj_cof_orth hn

theorem ordProj_pow_add_one_le (h : Setup s q q) {n : ℕ} (hn : 1 ≤ n)
    (hs : s ∣ q ^ n + 1) (he : ord s q ≠ 2 * n) : ordProj[s] (q ^ n + 1) ≤ q ^ (n - 1) := by
  have hq1 := h.one_le
  have h1 : 1 ≤ q ^ n := Nat.one_le_pow _ _ hq1
  have hsplit : fac (q : ℤ) (2 * n) = (q ^ n - 1) * (q ^ n + 1) := by
    have h2 : 1 ≤ q ^ (2 * n) := Nat.one_le_pow _ _ hq1
    rw [fac_natCast hq1]
    zify [h1, h2]
    ring
  have hnd : ¬ s ∣ q ^ n - 1 := fun hd => h.not_dvd_two (by
    have h2 : q ^ n + 1 = (q ^ n - 1) + 2 := by omega
    rw [h2] at hs
    exact (Nat.dvd_add_right hd).mp hs)
  have hnd' : ¬ ord s q ∣ n := fun hd => hnd (by
    rw [← fac_natCast hq1]
    exact (h.dvd_fac_iff n).mpr hd)
  have hd2 : ord s q ∣ 2 * n := (h.dvd_fac_iff _).mp (by
    rw [hsplit]
    exact Dvd.dvd.mul_left hs _)
  have hne1 : q ^ n - 1 ≠ 0 := by
    have := (fac_natCast hq1 n) ▸ h.fac_ne_zero (d := n) (by omega)
    exact this
  have hval : ordProj[s] (q ^ n + 1) = ordProj[s] (fac (q : ℤ) (2 * n)) := by
    rw [hsplit, Nat.ordProj_mul s hne1 (by omega), Nat.factorization_eq_zero_of_not_dvd hnd,
      pow_zero, one_mul]
  obtain ⟨m, hm⟩ := hd2
  have heven : Even (ord s q) := by
    rcases Nat.even_or_odd (ord s q) with h' | h'
    · exact h'
    · exact absurd (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr h')
        ⟨m, hm⟩) hnd'
  obtain ⟨k, hk⟩ := heven
  have hpos := h.ord_pos
  have hm3 : 3 ≤ m := by
    rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ 3 ≤ m by omega) with rfl | rfl | rfl | h3
    · omega
    · omega
    · exact absurd ⟨1, by omega⟩ hnd'
    · exact h3
  have hkm : k * m = n := by
    have : (k + k) * m = 2 * n := by rw [← hk]; exact hm.symm
    nlinarith
  rw [hval, hm]
  calc ordProj[s] (fac (q : ℤ) (ord s q * m)) ≤ q ^ (k * m - 1) :=
        h.ordProj_fac_ord_mul_le hm3 (by omega) (h.ordProj_fac_ord_le_half (by omega))
    _ = q ^ (n - 1) := by rw [hkm]

theorem ordProj_cof_orthMinus_even (h : Setup s q q) {n : ℕ} (hn : 2 ≤ n) :
    ordProj[s] ((q ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) ≤ q ^ (n * (n - 1)) := by
  have hq1 := h.one_le
  rw [← Finset.prod_congr rfl fun i _ => fac_natCast hq1 _]
  have hmem : ∀ i ∈ Icc 1 (n - 1), 1 ≤ i := fun i hi => (Finset.mem_Icc.mp hi).1
  have hP0 : ∏ i ∈ Icc 1 (n - 1), fac (q : ℤ) (2 * i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => h.fac_ne_zero (by have := hmem i hi; omega)
  have hP := h.ordProj_prod_fac_even_le (m := n - 1) (by omega)
  rw [sum_Icc_one_two_mul_sub_one] at hP
  rw [Nat.ordProj_mul s (by omega) hP0]
  by_cases hs : s ∣ q ^ n + 1
  · by_cases he : ord s q = 2 * n
    ·
      have hP1 : ordProj[s] (∏ i ∈ Icc 1 (n - 1), fac (q : ℤ) (2 * i)) = 1 := by
        rw [ordProj_prod fun i hi => h.fac_ne_zero (by have := hmem i hi; omega)]
        refine Finset.prod_eq_one fun i hi => ?_
        have hi := Finset.mem_Icc.mp hi
        rw [h.factorization_fac_eq_zero, pow_zero]
        rw [he]
        intro hd
        have := Nat.le_of_dvd (by omega) hd
        omega
      rw [hP1, mul_one]
      have hlt := ordProj_lt_of_even h.odd_s (x := q ^ n + 1) (by omega)
        (h.odd_q.pow.add_odd odd_one)
      calc ordProj[s] (q ^ n + 1) ≤ q ^ n := by omega
        _ ≤ q ^ (n * (n - 1)) := Nat.pow_le_pow_right (by omega)
          (Nat.le_mul_of_pos_right n (by omega))
    · calc ordProj[s] (q ^ n + 1) * ordProj[s] (∏ i ∈ Icc 1 (n - 1), fac (q : ℤ) (2 * i))
          ≤ q ^ (n - 1) * q ^ ((n - 1) ^ 2) :=
            Nat.mul_le_mul (h.ordProj_pow_add_one_le (by omega) hs he) hP
        _ = q ^ (n * (n - 1)) := by rw [← pow_add, sub_one_add_sq_sub_one (by omega)]
  · rw [Nat.factorization_eq_zero_of_not_dvd hs, pow_zero, one_mul]
    calc ordProj[s] (∏ i ∈ Icc 1 (n - 1), fac (q : ℤ) (2 * i)) ≤ q ^ ((n - 1) ^ 2) := hP
      _ ≤ q ^ (n * (n - 1)) := Nat.pow_le_pow_right (by omega) (by
          rw [← sub_one_add_sq_sub_one (by omega : 1 ≤ n)]
          omega)

theorem ordProj_cof_orthMinus (h : Setup s q q) (h' : Setup s q (-(q : ℤ))) {n : ℕ}
    (hn : 2 ≤ n) :
    ordProj[s] ((q ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) ≤ q ^ (n * (n - 1)) := by
  rcases Nat.even_or_odd n with hev | hodd
  · exact h.ordProj_cof_orthMinus_even hn
  · rw [← fac_neg_of_odd hodd, ← Finset.prod_congr rfl fun i _ =>
      fac_neg_of_even h.one_le (even_two_mul i)]
    exact h'.ordProj_cof_orth hn

theorem ordProj_cof_trialityD4 (h : Setup s q q) :
    ordProj[s] ((q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) ≤ q ^ 12 := by
  have hq1 := h.one_le
  have hA : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right hq1 (by norm_num)
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq1
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have key : (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) =
      (q ^ 4 - q ^ 2 + 1) * ((q ^ 6 - 1) * (q ^ 6 - 1)) := by
    zify [hA, h6, h2]
    ring
  have hAB : (q ^ 4 - q ^ 2 + 1) * (q ^ 2 + 1) = (q ^ 6 - 1) + 2 := by
    zify [hA, h6]
    ring
  have hB : fac (q : ℤ) 6 = q ^ 6 - 1 := fac_natCast hq1 6
  have hB0 : q ^ 6 - 1 ≠ 0 := hB ▸ h.fac_ne_zero (by norm_num)
  have hBle : ordProj[s] (q ^ 6 - 1) ≤ q ^ 6 := hB ▸ h.ordProj_fac_le (by norm_num)
  rw [key, Nat.ordProj_mul s (by omega) (mul_ne_zero hB0 hB0), Nat.ordProj_mul s hB0 hB0]
  by_cases hs : s ∣ q ^ 4 - q ^ 2 + 1
  · have hsB : ¬ s ∣ q ^ 6 - 1 := fun hd => h.not_dvd_two ((Nat.dvd_add_right hd).mp (by
      rw [← hAB]
      exact Dvd.dvd.mul_right hs _))
    rw [Nat.factorization_eq_zero_of_not_dvd hsB, pow_zero, mul_one, mul_one]
    calc ordProj[s] (q ^ 4 - q ^ 2 + 1) ≤ q ^ 4 - q ^ 2 + 1 := Nat.ordProj_le s (by omega)
      _ ≤ q ^ 12 := by
        have : q ^ 4 ≤ q ^ 12 := Nat.pow_le_pow_right hq1 (by norm_num)
        omega
  · rw [Nat.factorization_eq_zero_of_not_dvd hs, pow_zero, one_mul]
    calc ordProj[s] (q ^ 6 - 1) * ordProj[s] (q ^ 6 - 1) ≤ q ^ 6 * q ^ 6 :=
          Nat.mul_le_mul hBle hBle
      _ = q ^ 12 := by rw [← pow_add]

theorem ordProj_cof_twistedG2 (h : Setup s q q) (h' : Setup s q (-(q : ℤ))) :
    ordProj[s] ((q ^ 3 + 1) * (q - 1)) ≤ q ^ 3 := by
  have hq1 := h.one_le
  have hq3 := h.three_le
  have hA : fac (-(q : ℤ)) 3 = q ^ 3 + 1 := fac_neg_of_odd (by decide)
  have hB : fac (q : ℤ) 1 = q - 1 := by rw [fac_natCast hq1, pow_one]
  rw [Nat.ordProj_mul s (by omega) (by omega)]
  by_cases hs : s ∣ q - 1
  · have hsA : ¬ s ∣ q ^ 3 + 1 := fun hd => h.not_dvd_two (by
      have h1 : q - 1 ∣ q ^ 3 - 1 := by simpa using Nat.sub_dvd_pow_sub_pow q 1 3
      have h2 : q ^ 3 + 1 = (q ^ 3 - 1) + 2 := by
        have : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq1
        omega
      rw [h2] at hd
      exact (Nat.dvd_add_right (hs.trans h1)).mp hd)
    rw [Nat.factorization_eq_zero_of_not_dvd hsA, pow_zero, one_mul]
    calc ordProj[s] (q - 1) ≤ q ^ 1 := hB ▸ h.ordProj_fac_le one_ne_zero
      _ ≤ q ^ 3 := Nat.pow_le_pow_right hq1 (by norm_num)
  · rw [Nat.factorization_eq_zero_of_not_dvd hs, pow_zero, mul_one]
    exact hA ▸ h'.ordProj_fac_le (by norm_num)

end Setup

theorem ordProj_lieOrderCofactor_le {t : StatedLieTag} {n p f s : ℕ}
    (hadm : StatedLieAdmissible t n p f) (hp2 : p ≠ 2) (hs : s.Prime) (hs2 : s ≠ 2)
    (hsp : s ≠ p) :
    ordProj[s] (lieOrderCofactor t n (p ^ f)) ≤ (p ^ f) ^ lieSylowExponent t n := by
  have hp := hadm.1
  have hf := hadm.2.1
  have h : Setup s (p ^ f) ((p ^ f : ℕ) : ℤ) :=
    setup_of hp hp2 hf hs hs2 hsp (Int.natAbs_natCast _)
  have h' : Setup s (p ^ f) (-((p ^ f : ℕ) : ℤ)) :=
    setup_of hp hp2 hf hs hs2 hsp (by rw [Int.natAbs_neg, Int.natAbs_natCast])
  cases t
  case PSL =>
    obtain ⟨-, -, hn, -, -⟩ := hadm
    exact h.ordProj_cof_PSL hn
  case PSU =>
    obtain ⟨-, -, hn, -⟩ := hadm
    exact h'.ordProj_cof_PSU (by omega)
  case PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    exact h.ordProj_cof_PSp (by omega)
  case POmegaOdd =>
    obtain ⟨-, -, hn, -⟩ := hadm
    exact h.ordProj_cof_PSp (by omega)
  case POmegaPlus =>
    obtain ⟨-, -, hn⟩ := hadm
    exact h.ordProj_cof_orthPlus (by omega)
  case POmegaMinus =>
    obtain ⟨-, -, hn⟩ := hadm
    exact h.ordProj_cof_orthMinus h' (by omega)
  case G2 =>
    refine h.le_of_eq_prod (D := {2, 6}) (by decide) (by decide) ?_
      (by simp only [lieSylowExponent]; decide)
    rw [Finset.prod_pair (by decide)]
    simp only [lieOrderCofactor, fac_natCast h.one_le]
    ring
  case F4 =>
    refine h.le_of_eq_prod (D := {2, 6, 8, 12}) (by decide) (by decide) ?_
      (by simp only [lieSylowExponent]; decide)
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_pair (by decide)]
    simp only [lieOrderCofactor, fac_natCast h.one_le]
    ring
  case E6 =>
    refine h.le_of_eq_prod (D := {2, 5, 6, 8, 9, 12}) (by decide) (by decide) ?_
      (by simp only [lieSylowExponent]; decide)
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_pair (by decide)]
    simp only [lieOrderCofactor, fac_natCast h.one_le]
    ring
  case E7 =>
    refine h.le_of_eq_prod (D := {2, 6, 8, 10, 12, 14, 18}) (by decide) (by decide) ?_
      (by simp only [lieSylowExponent]; decide)
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_pair (by decide)]
    simp only [lieOrderCofactor, fac_natCast h.one_le]
    ring
  case E8 =>
    refine h.le_of_eq_prod (D := {2, 8, 12, 14, 18, 20, 24, 30}) (by decide) (by decide) ?_
      (by simp only [lieSylowExponent]; decide)
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_pair (by decide)]
    simp only [lieOrderCofactor, fac_natCast h.one_le]
    ring
  case twistedE6 =>
    refine h'.le_of_eq_prod (D := {2, 5, 6, 8, 9, 12}) (by decide) (by decide) ?_
      (by simp only [lieSylowExponent]; decide)
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_pair (by decide)]
    have h1 := h.one_le
    simp only [lieOrderCofactor, fac_neg_of_even h1 (by decide : Even 2),
      fac_neg_of_odd (by decide : Odd 5), fac_neg_of_even h1 (by decide : Even 6),
      fac_neg_of_even h1 (by decide : Even 8), fac_neg_of_odd (by decide : Odd 9),
      fac_neg_of_even h1 (by decide : Even 12)]
    ring
  case trialityD4 => exact h.ordProj_cof_trialityD4
  case twistedB2 =>
    obtain ⟨-, -, -, rfl, -⟩ := hadm
    exact absurd rfl hp2
  case twistedF4 =>
    obtain ⟨-, -, -, rfl, -⟩ := hadm
    exact absurd rfl hp2
  case twistedG2 => exact h.ordProj_cof_twistedG2 h'
  case Tits =>
    obtain ⟨-, -, -, rfl, -⟩ := hadm
    exact absurd rfl hp2

end CFSG.ComponentClassification.GS82PumpInputs.OddChar
