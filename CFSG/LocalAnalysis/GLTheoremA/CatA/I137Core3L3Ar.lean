module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3List

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I137C3

open CFSG.Open

theorem l3_two_pow_mul_odd_inj {m k Y Z : ℕ} (hY : Odd Y) (hZ : Odd Z)
    (h : 2 ^ m * Y = 2 ^ k * Z) : m = k ∧ Y = Z := by
  rcases lt_trichotomy m k with hlt | rfl | hgt
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have h1 : 2 ^ m * Y = 2 ^ m * (2 ^ (d + 1) * Z) := by rw [h, pow_succ, pow_add]; ring
    have h2 := Nat.eq_of_mul_eq_mul_left (by positivity) h1
    have : Even Y := by
      rw [h2]
      exact (even_two.pow_of_ne_zero (Nat.succ_ne_zero d)).mul_right Z
    exact (Nat.not_even_iff_odd.2 hY) this
  · exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    have h1 : 2 ^ k * Z = 2 ^ k * (2 ^ (d + 1) * Y) := by rw [← h, pow_succ, pow_add]; ring
    have h2 := Nat.eq_of_mul_eq_mul_left (by positivity) h1
    have : Even Z := by
      rw [h2]
      exact (even_two.pow_of_ne_zero (Nat.succ_ne_zero d)).mul_right Y
    exact (Nat.not_even_iff_odd.2 hZ) this

theorem l3_odd_four_pow_sub_one {m : ℕ} (hm : 1 ≤ m) : Odd (4 ^ m - 1) := by
  have h2 : 2 ∣ 4 ^ m := dvd_pow (by norm_num) (by omega)
  have h4 : 4 ≤ 4 ^ m := by
    calc 4 = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  exact Nat.odd_iff.2 (by omega)

theorem l3_fixed_ne {N : ℕ} (hN : N ∈ list93FixedOrders) {m : ℕ} (hm : 2 ≤ m) :
    N ≠ 2 ^ m * (4 ^ m - 1) := by
  intro h
  have hb : ∀ n ∈ list93FixedOrders, n < 2 ^ 90 := by decide +kernel
  have hlt : m < 100 := by
    by_contra hge
    have h4 : 4 ≤ 4 ^ m := by
      calc 4 = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 2 ^ m ≤ 2 ^ m * (4 ^ m - 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have h2 : 2 ^ 100 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ 90 ≤ 2 ^ 100 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := hb N hN
    omega
  have key : ∀ n ∈ list93FixedOrders, ∀ k < 100, 2 ≤ k → n ≠ 2 ^ k * (4 ^ k - 1) := by
    decide +kernel
  exact key N hN m hlt hm h

theorem l3_three_dvd_two_pow_sub_one {e : ℕ} (he : Even e) : 3 ∣ 2 ^ e - 1 := by
  have h := Core3Arith.two_pow_mod_three_of_even he
  have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  omega

theorem l3_three_dvd_two_pow_add_one {e : ℕ} (he : Odd e) : 3 ∣ 2 ^ e + 1 := by
  have h := Core3Arith.two_pow_mod_three_of_odd he
  omega

theorem l3_pow_five_lt {a : ℕ} (ha : 2 ≤ a) : a ^ 5 < 3 * (a ^ 6 - 1) := by
  have h5 : 32 ≤ a ^ 5 := by
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ a ^ 5 := Nat.pow_le_pow_left ha 5
  have h6 : 2 * a ^ 5 ≤ a ^ 6 := by
    rw [pow_succ]
    nlinarith
  omega

theorem l3_mul_sub_one_le (a : ℕ) : (a ^ 2 - 1) * (a ^ 3 - 1) ≤ a ^ 5 := by
  calc (a ^ 2 - 1) * (a ^ 3 - 1) ≤ a ^ 2 * a ^ 3 :=
        Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
    _ = a ^ 5 := by ring

theorem l3_sq_sub_one {a : ℕ} (ha : 1 ≤ a) : a ^ 2 - 1 = (a - 1) * (a + 1) := by
  zify [ha, show 1 ≤ a ^ 2 from Nat.one_le_pow _ _ ha]
  ring

theorem l3_orderA_ne {e : ℕ} (he : 2 ≤ e) (hev : Even e) {m : ℕ} (hm : 2 ≤ m) :
    orderA 2 (2 ^ e) ≠ 2 ^ m * (4 ^ m - 1) := by
  intro h
  have ha2 : 4 ≤ 2 ^ e := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have heven : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
  have h3 := l3_three_dvd_two_pow_sub_one hev
  generalize ha : 2 ^ e = a at *
  rw [Core3Arith.orderA_two, Nat.gcd_eq_left h3] at h
  have hd1 : a - 1 ∣ a ^ 2 - 1 := ⟨a + 1, l3_sq_sub_one (by omega)⟩
  obtain ⟨X, hX⟩ : 3 ∣ (a ^ 2 - 1) * (a ^ 3 - 1) := (h3.trans hd1).mul_right _
  have h1 : a ^ 3 * (3 * X) / 3 = a ^ 3 * X := by
    rw [mul_left_comm]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  rw [hX, h1] at h
  have hodd1 : Odd (a ^ 2 - 1) := by
    have : 2 ∣ a ^ 2 := dvd_pow heven (by norm_num)
    have : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by omega)
    exact Nat.odd_iff.2 (by omega)
  have hodd2 : Odd (a ^ 3 - 1) := by
    have : 2 ∣ a ^ 3 := dvd_pow heven (by norm_num)
    have : 1 ≤ a ^ 3 := Nat.one_le_pow _ _ (by omega)
    exact Nat.odd_iff.2 (by omega)
  have hX3 : Odd (3 * X) := by rw [← hX]; exact hodd1.mul hodd2
  have hXodd : Odd X := (Nat.odd_mul.1 hX3).2
  have hYodd := l3_odd_four_pow_sub_one (m := m) (by omega)
  have ha3 : a ^ 3 = 2 ^ (3 * e) := by rw [← ha, ← pow_mul, mul_comm]
  have hcomm : 2 ^ m * (4 ^ m - 1) = 2 ^ (3 * e) * X := by rw [← ha3, h]
  obtain ⟨hm3, hXY⟩ := l3_two_pow_mul_odd_inj hYodd hXodd hcomm
  have h46 : 4 ^ m = a ^ 6 := by
    rw [hm3, ← ha, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [h46] at hXY
  have hle := l3_mul_sub_one_le a
  have hlt := l3_pow_five_lt (a := a) (by omega)
  rw [hX, ← hXY] at hle
  omega

theorem l3_orderTwistedA_ne {e : ℕ} (he : 3 ≤ e) (hodd : Odd e) {m : ℕ} (hm : 2 ≤ m) :
    orderTwistedA 2 (2 ^ e) ≠ 2 ^ m * (4 ^ m - 1) := by
  intro h
  have ha2 : 8 ≤ 2 ^ e := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have heven : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
  have h3 := l3_three_dvd_two_pow_add_one hodd
  generalize ha : 2 ^ e = a at *
  rw [Core3Arith.orderTwistedA_two, Nat.gcd_eq_left h3] at h
  have hd1 : a + 1 ∣ a ^ 2 - 1 := ⟨a - 1, by rw [l3_sq_sub_one (by omega), mul_comm]⟩
  obtain ⟨X, hX⟩ : 3 ∣ (a ^ 2 - 1) * (a ^ 3 + 1) := (h3.trans hd1).mul_right _
  have h1 : a ^ 3 * (3 * X) / 3 = a ^ 3 * X := by
    rw [mul_left_comm]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  rw [hX, h1] at h
  have hodd1 : Odd (a ^ 2 - 1) := by
    have : 2 ∣ a ^ 2 := dvd_pow heven (by norm_num)
    have : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by omega)
    exact Nat.odd_iff.2 (by omega)
  have hodd2 : Odd (a ^ 3 + 1) := by
    have : 2 ∣ a ^ 3 := dvd_pow heven (by norm_num)
    exact Nat.odd_iff.2 (by omega)
  have hX3 : Odd (3 * X) := by rw [← hX]; exact hodd1.mul hodd2
  have hXodd : Odd X := (Nat.odd_mul.1 hX3).2
  have hYodd := l3_odd_four_pow_sub_one (m := m) (by omega)
  have ha3 : a ^ 3 = 2 ^ (3 * e) := by rw [← ha, ← pow_mul, mul_comm]
  have hcomm : 2 ^ m * (4 ^ m - 1) = 2 ^ (3 * e) * X := by rw [← ha3, h]
  obtain ⟨hm3, hXY⟩ := l3_two_pow_mul_odd_inj hYodd hXodd hcomm
  have h46 : 4 ^ m = a ^ 6 := by
    rw [hm3, ← ha, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [h46] at hXY
  have hle : (a ^ 2 - 1) * (a ^ 3 + 1) ≤ 2 * a ^ 5 := by
    calc (a ^ 2 - 1) * (a ^ 3 + 1) ≤ a ^ 2 * (a ^ 3 + 1) :=
          Nat.mul_le_mul (Nat.sub_le _ _) le_rfl
      _ = a ^ 5 + a ^ 2 := by ring
      _ ≤ a ^ 5 + a ^ 5 := by
          have : a ^ 2 ≤ a ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
          omega
      _ = 2 * a ^ 5 := by ring
  have h2 : 2 * a ^ 5 < 3 * (a ^ 6 - 1) := by
    have h5 : 32 ≤ a ^ 5 := by
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ a ^ 5 := Nat.pow_le_pow_left (by omega) 5
    have h6 : 2 * a ^ 5 ≤ a ^ 6 := by
      rw [pow_succ]
      nlinarith
    omega
  rw [hX, ← hXY] at hle
  omega

end CFSG.LocalAnalysis.GLTheoremA.I137C3

end
