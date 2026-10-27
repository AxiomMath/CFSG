module

public import CFSG.Open.Defs

public section

namespace CFSG.EvenSporadicStandard.Induction

open CFSG.Open

theorem orderOf_two_zmod_twentyNine : orderOf (2 : ZMod 29) = 28 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hm0
  interval_cases m <;> decide

theorem dvd_of_dvd_two_pow_sub_one {k : ℕ} (h : 29 ∣ 2 ^ k - 1) : 28 ∣ k := by
  have h1 : ((2 ^ k - 1 : ℕ) : ZMod 29) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
  have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h2 : (2 : ZMod 29) ^ k = 1 := by
    rw [Nat.cast_sub hk] at h1
    push_cast at h1
    exact sub_eq_zero.1 h1
  rw [← orderOf_two_zmod_twentyNine]
  exact orderOf_dvd_of_pow_eq_one h2

theorem seven_dvd_of_dvd_two_pow {k : ℕ} (h : 29 ∣ 2 ^ k - 1 ∨ 29 ∣ 2 ^ k + 1) : 7 ∣ k := by
  rcases h with h | h
  · have := dvd_of_dvd_two_pow_sub_one h
    omega
  · have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h2 : 29 ∣ 2 ^ (2 * k) - 1 := by
      have : 2 ^ (2 * k) - 1 = (2 ^ k - 1) * (2 ^ k + 1) := by
        have e : 2 ^ (2 * k) = 2 ^ k * 2 ^ k := by rw [two_mul, pow_add]
        rw [e]
        zify [hk, Nat.one_le_iff_ne_zero.mpr (by positivity : 2 ^ k * 2 ^ k ≠ 0)]
        ring
      rw [this]
      exact Dvd.dvd.mul_left h _
    have := dvd_of_dvd_two_pow_sub_one h2
    omega

theorem dvd29_two_pow_four_mul {m : ℕ} (hm : 7 ∣ m) : 29 ∣ 2 ^ (4 * m) - 1 := by
  obtain ⟨j, rfl⟩ := hm
  have h1 : (2 : ℕ) ^ 28 - 1 ∣ ((2 : ℕ) ^ 28) ^ j - 1 ^ j := Nat.sub_dvd_pow_sub_pow _ 1 j
  have h2 : 29 ∣ (2 : ℕ) ^ 28 - 1 := by norm_num
  have h3 : 2 ^ (4 * (7 * j)) = ((2 : ℕ) ^ 28) ^ j := by rw [← pow_mul]; ring_nf
  rw [h3]
  simpa using h2.trans h1

theorem not_dvd29_pow_two_pow (m e : ℕ) : ¬ 29 ∣ (2 ^ m) ^ e := by
  intro h
  have h1 := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 29) h
  have h2 := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 29) h1
  omega

theorem dvd29_div_iff {N g : ℕ} (hgN : g ∣ N) (hg0 : 0 < g) (hg29 : g < 29) :
    29 ∣ N / g ↔ 29 ∣ N := by
  obtain ⟨c, rfl⟩ := hgN
  rw [Nat.mul_div_cancel_left c hg0]
  constructor
  · intro h
    exact Dvd.dvd.mul_left h g
  · intro h
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 29)).1 h with h | h
    · exact absurd (Nat.le_of_dvd hg0 h) (by omega)
    · exact h

theorem seven_dvd_mul_of_dvd_pow_pm {m i : ℕ} (h : 29 ∣ (2 ^ m) ^ i - 1 ∨ 29 ∣ (2 ^ m) ^ i + 1) :
    7 ∣ m * i := by
  rw [← pow_mul] at h
  exact seven_dvd_of_dvd_two_pow h

theorem seven_dvd_of_mul {m i : ℕ} (hi1 : 1 ≤ i) (hi6 : i ≤ 6) (h : 7 ∣ m * i) : 7 ∣ m := by
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).1 h with h | h
  · exact h
  · exact absurd (Nat.le_of_dvd (by omega) h) (by omega)

theorem dvd29_pow_four {m : ℕ} (hm : 7 ∣ m) : 29 ∣ (2 ^ m) ^ 4 - 1 := by
  have := dvd29_two_pow_four_mul hm
  rwa [← pow_mul, mul_comm]

section Families

theorem dvd29_ordA {n m : ℕ} (hn3 : 3 ≤ n) (hn4 : n ≤ 4) :
    29 ∣ ordA n (2 ^ m) ↔ 7 ∣ m := by
  unfold ordA
  have hq1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hg0 : 0 < Nat.gcd (n + 1) (2 ^ m - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hg29 : Nat.gcd (n + 1) (2 ^ m - 1) < 29 :=
    lt_of_le_of_lt (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)) (by omega)
  have hP2 : (2 ^ m) ^ 2 - 1 ∣ ∏ i ∈ Finset.Icc 2 (n + 1), ((2 ^ m) ^ i - 1) :=
    Finset.dvd_prod_of_mem (fun i => (2 ^ m) ^ i - 1) (by rw [Finset.mem_Icc]; omega)
  have hsub : 2 ^ m - 1 ∣ (2 ^ m) ^ 2 - 1 := by
    simpa using Nat.sub_dvd_pow_sub_pow (2 ^ m) 1 2
  have hg : Nat.gcd (n + 1) (2 ^ m - 1) ∣
      (2 ^ m) ^ (n * (n + 1) / 2) * ∏ i ∈ Finset.Icc 2 (n + 1), ((2 ^ m) ^ i - 1) :=
    Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans (hsub.trans hP2)) _
  rw [dvd29_div_iff hg hg0 hg29]
  constructor
  · intro h
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 29)).1 h with h | h
    · exact absurd h (not_dvd29_pow_two_pow _ _)
    · obtain ⟨i, hi, hdvd⟩ :=
        (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp (by norm_num : Nat.Prime 29)) _).1 h
      rw [Finset.mem_Icc] at hi
      exact seven_dvd_of_mul (i := i) (by omega) (by omega)
        (seven_dvd_mul_of_dvd_pow_pm (Or.inl hdvd))
  · intro h7
    refine Dvd.dvd.mul_left ?_ _
    exact (dvd29_pow_four h7).trans
      (Finset.dvd_prod_of_mem (fun i => (2 ^ m) ^ i - 1) (by rw [Finset.mem_Icc]; omega))

theorem toNat_pow_sub_neg_one_pow_even {q : ℕ} (hq : 1 ≤ q) {i : ℕ} (hi : Even i) :
    ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat = q ^ i - 1 := by
  have hqi : 1 ≤ q ^ i := Nat.one_le_pow _ _ hq
  have hc : ((q : ℤ) ^ i) = ((q ^ i : ℕ) : ℤ) := by push_cast; rfl
  rw [hc, hi.neg_one_pow]
  omega

theorem toNat_pow_sub_neg_one_pow_odd {q : ℕ} (hq : 1 ≤ q) {i : ℕ} (hi : Odd i) :
    ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat = q ^ i + 1 := by
  have hqi : 1 ≤ q ^ i := Nat.one_le_pow _ _ hq
  have hc : ((q : ℤ) ^ i) = ((q ^ i : ℕ) : ℤ) := by push_cast; rfl
  rw [hc, hi.neg_one_pow]
  omega

theorem dvd29_ordTwistedA {n m : ℕ} (hn3 : 3 ≤ n) (hn4 : n ≤ 4) :
    29 ∣ ordTwistedA n (2 ^ m) ↔ 7 ∣ m := by
  unfold ordTwistedA
  have hq1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hg0 : 0 < Nat.gcd (n + 1) (2 ^ m + 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hg29 : Nat.gcd (n + 1) (2 ^ m + 1) < 29 :=
    lt_of_le_of_lt (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)) (by omega)
  have hP2 : ((2 ^ m : ℕ) ^ 2 - 1) ∣ ∏ i ∈ Finset.Icc 2 (n + 1),
      (((2 ^ m : ℕ) : ℤ) ^ i - (-1 : ℤ) ^ i).toNat := by
    have h2 := Finset.dvd_prod_of_mem
      (fun i => (((2 ^ m : ℕ) : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) (by
        rw [Finset.mem_Icc]; omega : 2 ∈ Finset.Icc 2 (n + 1))
    rw [toNat_pow_sub_neg_one_pow_even hq1 even_two] at h2
    exact h2
  have hsub : 2 ^ m + 1 ∣ (2 ^ m) ^ 2 - 1 := by
    have h : (2 ^ m) ^ 2 - 1 = (2 ^ m + 1) * (2 ^ m - 1) := by
      zify [hq1, (by nlinarith : 1 ≤ (2 ^ m) ^ 2)]
      ring
    rw [h]
    exact Dvd.intro _ rfl
  have hg : Nat.gcd (n + 1) (2 ^ m + 1) ∣ (2 ^ m) ^ (n * (n + 1) / 2) *
      ∏ i ∈ Finset.Icc 2 (n + 1), (((2 ^ m : ℕ) : ℤ) ^ i - (-1 : ℤ) ^ i).toNat :=
    Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans (hsub.trans hP2)) _
  rw [dvd29_div_iff hg hg0 hg29]
  constructor
  · intro h
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 29)).1 h with h | h
    · exact absurd h (not_dvd29_pow_two_pow _ _)
    · obtain ⟨i, hi, hdvd⟩ :=
        (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp (by norm_num : Nat.Prime 29)) _).1 h
      rw [Finset.mem_Icc] at hi
      refine seven_dvd_of_mul (i := i) (by omega) (by omega) (seven_dvd_mul_of_dvd_pow_pm ?_)
      rcases Nat.even_or_odd i with he | ho
      · rw [toNat_pow_sub_neg_one_pow_even hq1 he] at hdvd
        exact Or.inl hdvd
      · rw [toNat_pow_sub_neg_one_pow_odd hq1 ho] at hdvd
        exact Or.inr hdvd
  · intro h7
    refine Dvd.dvd.mul_left ?_ _
    have h4 := Finset.dvd_prod_of_mem
      (fun i => (((2 ^ m : ℕ) : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) (by
        rw [Finset.mem_Icc]; omega : 4 ∈ Finset.Icc 2 (n + 1))
    rw [toNat_pow_sub_neg_one_pow_even hq1 (by decide : Even 4)] at h4
    exact (dvd29_pow_four h7).trans h4

theorem dvd29_ordBC_two (m : ℕ) : 29 ∣ ordBC 2 (2 ^ m) ↔ 7 ∣ m := by
  unfold ordBC
  have hq1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hg0 : 0 < Nat.gcd 2 (2 ^ m - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hg29 : Nat.gcd 2 (2 ^ m - 1) < 29 :=
    lt_of_le_of_lt (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)) (by omega)
  have hP1 : (2 ^ m) ^ (2 * 1) - 1 ∣ ∏ i ∈ Finset.Icc 1 2, ((2 ^ m) ^ (2 * i) - 1) :=
    Finset.dvd_prod_of_mem (fun i => (2 ^ m) ^ (2 * i) - 1) (by rw [Finset.mem_Icc]; omega)
  have hsub : 2 ^ m - 1 ∣ (2 ^ m) ^ (2 * 1) - 1 := by
    simpa using Nat.sub_dvd_pow_sub_pow (2 ^ m) 1 2
  have hg : Nat.gcd 2 (2 ^ m - 1) ∣
      (2 ^ m) ^ (2 * 2) * ∏ i ∈ Finset.Icc 1 2, ((2 ^ m) ^ (2 * i) - 1) :=
    Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans (hsub.trans hP1)) _
  rw [dvd29_div_iff hg hg0 hg29]
  constructor
  · intro h
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 29)).1 h with h | h
    · exact absurd h (not_dvd29_pow_two_pow _ _)
    · obtain ⟨i, hi, hdvd⟩ :=
        (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp (by norm_num : Nat.Prime 29)) _).1 h
      rw [Finset.mem_Icc] at hi
      have h7 := seven_dvd_mul_of_dvd_pow_pm (Or.inl hdvd)
      have h7' : 7 ∣ m * (2 * i) := h7
      have : 7 ∣ m * (2 * i) → 7 ∣ m := fun h =>
        seven_dvd_of_mul (i := 2 * i) (by omega) (by omega) h
      exact this h7'
  · intro h7
    refine Dvd.dvd.mul_left ?_ _
    have h4 : 29 ∣ (2 ^ m) ^ (2 * 2) - 1 := dvd29_pow_four h7
    exact h4.trans (Finset.dvd_prod_of_mem (fun i => (2 ^ m) ^ (2 * i) - 1)
      (by rw [Finset.mem_Icc]; omega : 2 ∈ Finset.Icc 1 2))

theorem dvd29_suzuki {f : ℕ} (hf : Odd f) :
    29 ∣ (2 ^ f) ^ 2 * (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) ↔ 7 ∣ f := by
  constructor
  · intro h
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 29)).1 h with h | h
    · rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 29)).1 h with h | h
      · exact absurd h (not_dvd29_pow_two_pow _ _)
      · exact seven_dvd_of_dvd_two_pow (Or.inl h)
    · have := seven_dvd_mul_of_dvd_pow_pm (m := f) (i := 2) (Or.inr h)
      exact seven_dvd_of_mul (i := 2) (by omega) (by omega) this
  · intro h7
    obtain ⟨j, hj⟩ := h7
    have hjodd : Odd j := by
      rcases Nat.even_or_odd j with h | h
      · exfalso
        obtain ⟨c, hc⟩ := h
        obtain ⟨d, hd⟩ := hf
        omega
      · exact h
    refine Dvd.dvd.mul_left ?_ _
    have h1 : (2 ^ 14 : ℕ) + 1 ∣ ((2 ^ 14 : ℕ)) ^ j + 1 ^ j := hjodd.nat_add_dvd_pow_add_pow _ 1
    have h2 : 29 ∣ (2 ^ 14 : ℕ) + 1 := by norm_num
    have h3 : (2 ^ f) ^ 2 = ((2 ^ 14 : ℕ)) ^ j := by
      rw [← pow_mul, ← pow_mul, hj]
      ring_nf
    rw [h3]
    simpa using h2.trans h1

end Families

end CFSG.EvenSporadicStandard.Induction
