module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

section LTE

theorem padicValNat_three_four_pow_sub_one {n : ℕ} (hn : n ≠ 0) (h3 : ¬ 3 ∣ n) :
    padicValNat 3 (4 ^ n - 1) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := padicValNat.pow_sub_pow (x := 4) (y := 1) (p := 3) (by decide) (by norm_num)
    (by norm_num) (by norm_num) hn
  rw [one_pow] at h
  rw [h, padicValNat.eq_zero_of_not_dvd h3, add_zero]
  exact padicValNat_self

theorem padicValNat_three_eight_pow_sub_one {n : ℕ} (hn : n ≠ 0) (he : Even n)
    (h3 : ¬ 3 ∣ n) : padicValNat 3 (8 ^ n - 1) = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, rfl⟩ := he
  have hm : m ≠ 0 := by omega
  have hm3 : ¬ 3 ∣ m := fun h => h3 (Dvd.dvd.add h h)
  have h8 : (8 : ℕ) ^ (m + m) = 64 ^ m := by
    rw [← two_mul, pow_mul]
    norm_num
  have h := padicValNat.pow_sub_pow (x := 64) (y := 1) (p := 3) (by decide) (by norm_num)
    (by norm_num) (by norm_num) hm
  rw [one_pow] at h
  rw [h8, h, padicValNat.eq_zero_of_not_dvd hm3, add_zero]
  have h63 : (64 : ℕ) - 1 = 3 ^ 2 * 7 := by norm_num
  rw [h63, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 7)]

theorem padicValNat_three_eight_pow_add_one {n : ℕ} (ho : Odd n) (h3 : ¬ 3 ∣ n) :
    padicValNat 3 (8 ^ n + 1) = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := padicValNat.pow_add_pow (x := 8) (y := 1) (p := 3) (by decide) (by norm_num)
    (by norm_num) ho
  rw [one_pow] at h
  rw [h, padicValNat.eq_zero_of_not_dvd h3, add_zero]
  have h9 : (8 : ℕ) + 1 = 3 ^ 2 := by norm_num
  rw [h9, padicValNat.prime_pow]

end LTE

theorem two_pow_three_mul (n : ℕ) : (2 : ℕ) ^ (3 * n) = 8 ^ n := by
  rw [pow_mul]
  norm_num

theorem two_pow_two_mul (n : ℕ) : (2 : ℕ) ^ (2 * n) = 4 ^ n := by
  rw [pow_mul]
  norm_num

theorem odd_four_pow_sub_one {n : ℕ} (hn : n ≠ 0) : Odd (4 ^ n - 1) := by
  have h1 : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have he : Even (4 ^ n) := (Nat.even_pow.2 ⟨by decide, hn⟩)
  rcases he with ⟨k, hk⟩
  exact ⟨k - 1, by omega⟩

theorem odd_eight_pow_sub_one {n : ℕ} (hn : n ≠ 0) : Odd (8 ^ n - 1) := by
  have h1 : 1 ≤ 8 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have he : Even (8 ^ n) := (Nat.even_pow.2 ⟨by decide, hn⟩)
  rcases he with ⟨k, hk⟩
  exact ⟨k - 1, by omega⟩

theorem odd_eight_pow_add_one {n : ℕ} (hn : n ≠ 0) : Odd (8 ^ n + 1) :=
  (Nat.even_pow.2 ⟨by decide, hn⟩).add_one

theorem L3U3Order.padicValNat_three {N : ℕ} (h : L3U3Order N) : padicValNat 3 N = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, ⟨hn6, hN⟩ | ⟨hn6, hn1, hN⟩⟩ := h
  · have hn : n ≠ 0 := by omega
    have h3 : ¬ 3 ∣ n := by omega
    have he : Even n := Nat.even_iff.2 (by omega)
    rw [two_pow_three_mul, two_pow_two_mul] at hN
    have h4 : 4 ^ n - 1 ≠ 0 := (odd_four_pow_sub_one hn).pos.ne'
    have h8 : 8 ^ n - 1 ≠ 0 := (odd_eight_pow_sub_one hn).pos.ne'
    have hN0 : N ≠ 0 := by
      rintro rfl
      simp only [mul_zero] at hN
      exact (mul_ne_zero (pow_ne_zero n (by norm_num)) (mul_ne_zero h4 h8)) hN.symm
    have h80 : padicValNat 3 (8 ^ n) = 0 := padicValNat.eq_zero_of_not_dvd fun h =>
      (by norm_num : ¬ 3 ∣ 8) (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
    have hv := congrArg (padicValNat 3) hN
    rw [padicValNat.mul (by norm_num) hN0, padicValNat_self,
      padicValNat.mul (pow_ne_zero n (by norm_num)) (mul_ne_zero h4 h8),
      padicValNat.mul h4 h8, padicValNat_three_four_pow_sub_one hn h3,
      padicValNat_three_eight_pow_sub_one hn he h3,
      h80] at hv
    omega
  · have hn : n ≠ 0 := by omega
    have h3 : ¬ 3 ∣ n := by omega
    have ho : Odd n := Nat.odd_iff.2 (by omega)
    rw [two_pow_three_mul, two_pow_two_mul] at hN
    have h4 : 4 ^ n - 1 ≠ 0 := (odd_four_pow_sub_one hn).pos.ne'
    have h8 : 8 ^ n + 1 ≠ 0 := by positivity
    have hN0 : N ≠ 0 := by
      rintro rfl
      simp only [mul_zero] at hN
      exact (mul_ne_zero (pow_ne_zero n (by norm_num)) (mul_ne_zero h4 h8)) hN.symm
    have h80 : padicValNat 3 (8 ^ n) = 0 := padicValNat.eq_zero_of_not_dvd fun h =>
      (by norm_num : ¬ 3 ∣ 8) (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
    have hv := congrArg (padicValNat 3) hN
    rw [padicValNat.mul (by norm_num) hN0, padicValNat_self,
      padicValNat.mul (pow_ne_zero n (by norm_num)) (mul_ne_zero h4 h8),
      padicValNat.mul h4 h8, padicValNat_three_four_pow_sub_one hn h3,
      padicValNat_three_eight_pow_add_one ho h3,
      h80] at hv
    omega

theorem L3U3Order.ne_zero {N : ℕ} (h : L3U3Order N) : N ≠ 0 := by
  rintro rfl
  have := h.padicValNat_three
  simp at this

theorem L3U3Order.padicValNat_two {N : ℕ} (h : L3U3Order N) :
    ∃ n : ℕ, ¬ 3 ∣ n ∧ 1 ≤ n ∧ padicValNat 2 N = 3 * n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN0 := h.ne_zero
  obtain ⟨n, ⟨hn6, hN⟩ | ⟨hn6, hn1, hN⟩⟩ := h
  · have hn : n ≠ 0 := by omega
    refine ⟨n, by omega, by omega, ?_⟩
    have h4 : Odd (2 ^ (2 * n) - 1) := by rw [two_pow_two_mul]; exact odd_four_pow_sub_one hn
    have h8 : Odd (2 ^ (3 * n) - 1) := by rw [two_pow_three_mul]; exact odd_eight_pow_sub_one hn
    have hn4 := Nat.odd_iff.1 h4
    have hn8 := Nat.odd_iff.1 h8
    have hv := congrArg (padicValNat 2) hN
    rw [padicValNat.mul (by norm_num) hN0,
      padicValNat.mul (pow_ne_zero _ (by norm_num)) (mul_ne_zero h4.pos.ne' h8.pos.ne'),
      padicValNat.mul h4.pos.ne' h8.pos.ne', padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3),
      padicValNat.eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.2 hn4),
      padicValNat.eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.2 hn8)] at hv
    omega
  · have hn : n ≠ 0 := by omega
    refine ⟨n, by omega, by omega, ?_⟩
    have h4 : Odd (2 ^ (2 * n) - 1) := by rw [two_pow_two_mul]; exact odd_four_pow_sub_one hn
    have h8 : Odd (2 ^ (3 * n) + 1) := by rw [two_pow_three_mul]; exact odd_eight_pow_add_one hn
    have hn4 := Nat.odd_iff.1 h4
    have hn8 := Nat.odd_iff.1 h8
    have hv := congrArg (padicValNat 2) hN
    rw [padicValNat.mul (by norm_num) hN0,
      padicValNat.mul (pow_ne_zero _ (by norm_num)) (mul_ne_zero h4.pos.ne' h8.pos.ne'),
      padicValNat.mul h4.pos.ne' h8.pos.ne', padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3),
      padicValNat.eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.2 hn4),
      padicValNat.eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.2 hn8)] at hv
    omega

theorem L3U3Order.not_27_dvd {N : ℕ} (h : L3U3Order N) : ¬ 27 ∣ N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h27
  have h3 := (padicValNat_dvd_iff_le h.ne_zero).1 (show 3 ^ 3 ∣ N by simpa using h27)
  rw [h.padicValNat_three] at h3
  omega

theorem L3U3Order.nine_dvd {N : ℕ} (h : L3U3Order N) : 9 ∣ N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := (padicValNat_dvd_iff_le (p := 3) (n := 2) h.ne_zero).2 h.padicValNat_three.ge
  simpa using this

theorem L3U3Order.cases {N : ℕ} (h : L3U3Order N) : (5 ∣ N ∧ 7 ∣ N) ∨ 366157135872 ≤ N := by
  obtain ⟨n, ⟨hn6, hN⟩ | ⟨hn6, hn1, hN⟩⟩ := h
  · left
    obtain ⟨m, rfl⟩ : Even n := Nat.even_iff.2 (by omega)
    rw [two_pow_three_mul, two_pow_two_mul] at hN
    have h5 : 5 ∣ 4 ^ (m + m) - 1 := by
      rw [← two_mul, pow_mul]
      norm_num
      exact dvd_trans (by norm_num : 5 ∣ 15) (by simpa using Nat.sub_dvd_pow_sub_pow 16 1 m)
    have h7 : 7 ∣ 8 ^ (m + m) - 1 := by
      simpa using Nat.sub_dvd_pow_sub_pow 8 1 (m + m)
    have h5' : 5 ∣ 3 * N := hN ▸ Dvd.dvd.mul_left (Dvd.dvd.mul_right h5 _) _
    have h7' : 7 ∣ 3 * N := hN ▸ Dvd.dvd.mul_left (Dvd.dvd.mul_left h7 _) _
    exact ⟨(Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h5'),
      (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h7')⟩
  · right
    have hn5 : 5 ≤ n := by omega
    have h1 : (2 : ℕ) ^ (3 * 5) ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (2 : ℕ) ^ (2 * 5) - 1 ≤ 2 ^ (2 * n) - 1 :=
      Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) (by omega)) 1
    have h3 : (2 : ℕ) ^ (3 * 5) + 1 ≤ 2 ^ (3 * n) + 1 :=
      Nat.add_le_add_right (Nat.pow_le_pow_right (by norm_num) (by omega)) 1
    have hle : 2 ^ (3 * 5) * ((2 ^ (2 * 5) - 1) * (2 ^ (3 * 5) + 1)) ≤
        2 ^ (3 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    rw [← hN] at hle
    norm_num at hle
    omega

theorem L3U3Order.ge_20160 {N : ℕ} (h : L3U3Order N) : 20160 ≤ N := by
  obtain ⟨n, ⟨hn6, hN⟩ | ⟨hn6, hn1, hN⟩⟩ := h
  · have hn2 : 2 ≤ n := by omega
    have h1 : (2 : ℕ) ^ (3 * 2) ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (2 : ℕ) ^ (2 * 2) - 1 ≤ 2 ^ (2 * n) - 1 :=
      Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) (by omega)) 1
    have h3 : (2 : ℕ) ^ (3 * 2) - 1 ≤ 2 ^ (3 * n) - 1 :=
      Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) (by omega)) 1
    have hle := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    rw [← hN] at hle
    norm_num at hle
    omega
  · have := (L3U3Order.cases ⟨n, Or.inr ⟨hn6, hn1, hN⟩⟩)
    rcases this with ⟨h5, h7⟩ | hge
    ·
      have hn5 : 5 ≤ n := by omega
      have h1 : (2 : ℕ) ^ (3 * 5) ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : (2 : ℕ) ^ (2 * 5) - 1 ≤ 2 ^ (2 * n) - 1 :=
        Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) (by omega)) 1
      have h3 : (2 : ℕ) ^ (3 * 5) + 1 ≤ 2 ^ (3 * n) + 1 :=
        Nat.add_le_add_right (Nat.pow_le_pow_right (by norm_num) (by omega)) 1
      have hle := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
      rw [← hN] at hle
      norm_num at hle
      omega
    · omega

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
