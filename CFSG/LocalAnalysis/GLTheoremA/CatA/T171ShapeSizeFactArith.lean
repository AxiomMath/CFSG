module

public import CFSG.Open.OrderForm
import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct
import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.FinalStepArith

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.CatDistinct

private def su6P (q : ℕ) : ℕ :=
  (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) * (q ^ 5 + 1) * (q ^ 6 - 1)

private def te6P (q : ℕ) : ℕ :=
  (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1)

private theorem orderTwistedE6_eq (q : ℕ) :
    orderTwistedE6 q = q ^ 36 * te6P q / Nat.gcd 3 (q + 1) := by
  simp only [orderTwistedE6, te6P, mul_assoc]

private theorem te6P_odd {n : ℕ} (hn : 1 ≤ n) : Odd (te6P (2 ^ n)) := by
  unfold te6P
  exact (((((odd_pow_two_pow_sub_one hn (by norm_num)).mul
    (odd_pow_two_pow_add_one hn (by norm_num))).mul
    (odd_pow_two_pow_sub_one hn (by norm_num))).mul
    (odd_pow_two_pow_sub_one hn (by norm_num))).mul
    (odd_pow_two_pow_add_one hn (by norm_num))).mul
    (odd_pow_two_pow_sub_one hn (by norm_num))

private theorem gcd_dvd_te6P {n : ℕ} (hn : 1 ≤ n) : Nat.gcd 3 (2 ^ n + 1) ∣ te6P (2 ^ n) := by
  have h9 : Nat.gcd 3 (2 ^ n + 1) ∣ (2 ^ n) ^ 9 + 1 := by
    have h := Odd.nat_add_dvd_pow_add_pow (2 ^ n) 1 (by decide : Odd 9)
    rw [one_pow] at h
    exact (Nat.gcd_dvd_right 3 (2 ^ n + 1)).trans h
  unfold te6P
  exact ((((Dvd.dvd.mul_left h9 _).mul_right _).mul_right _).mul_right _).mul_right _

theorem two_part_orderTwistedE6 {n : ℕ} (hn : 1 ≤ n) :
    ∃ A, Odd A ∧ orderTwistedE6 (2 ^ n) = 2 ^ (36 * n) * A := by
  set q := 2 ^ n with hq
  set g := Nat.gcd 3 (q + 1) with hg
  obtain ⟨A, hA⟩ := gcd_dvd_te6P hn
  have hoddP : Odd (te6P q) := by simpa [hq] using te6P_odd hn
  have hoddA : Odd A := by
    rw [hA] at hoddP
    exact Nat.Odd.of_mul_right hoddP
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by norm_num)
  refine ⟨A, hoddA, ?_⟩
  have h := orderTwistedE6_eq q
  rw [hA] at h
  rw [h]
  rw [show q ^ 36 * (g * A) = g * (q ^ 36 * A) by ring,
    Nat.mul_div_cancel_left _ hgpos]
  rw [hq, ← pow_mul, Nat.mul_comm n 36]

private theorem pow_twenty_le_eight_su6P {q : ℕ} (hq : 2 ≤ q) :
    q ^ 20 ≤ 8 * su6P q := by
  have h2 : q ^ 2 ≤ 2 * (q ^ 2 - 1) := by
    have h : 2 ≤ q ^ 2 := by
      have h' := Nat.pow_le_pow_left hq 2
      norm_num at h'
      omega
    omega
  have h3 : q ^ 3 ≤ q ^ 3 + 1 := Nat.le_add_right _ _
  have h4 : q ^ 4 ≤ 2 * (q ^ 4 - 1) := by
    have h : 2 ≤ q ^ 4 := by
      have h' := Nat.pow_le_pow_left hq 4
      norm_num at h'
      omega
    omega
  have h5 : q ^ 5 ≤ q ^ 5 + 1 := Nat.le_add_right _ _
  have h6 : q ^ 6 ≤ 2 * (q ^ 6 - 1) := by
    have h : 2 ≤ q ^ 6 := by
      have h' := Nat.pow_le_pow_left hq 6
      norm_num at h'
      omega
    omega
  unfold su6P
  calc q ^ 20 = ((((q ^ 2 * q ^ 3) * q ^ 4) * q ^ 5) * q ^ 6) := by ring
    _ ≤ ((((2 * (q ^ 2 - 1) * (q ^ 3 + 1)) * (2 * (q ^ 4 - 1))) * (q ^ 5 + 1)) *
        (2 * (q ^ 6 - 1))) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h2 h3) h4) h5) h6
    _ = 8 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) * (q ^ 5 + 1) * (q ^ 6 - 1)) := by ring

theorem pow_thirtyfive_le_orderTwistedA_five {n : ℕ} (hn : 1 ≤ n) :
    (2 ^ n) ^ 35 ≤ 48 * orderTwistedA 5 (2 ^ n) := by
  set q := 2 ^ n with hq
  have hq2 : 2 ≤ q := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ q := Nat.pow_le_pow_right (by norm_num) hn
  have h := orderTwistedA_mul_gcd (r := 5) (m := n) (by norm_num) hn
  rw [twP_five, show 5 * (5 + 1) / 2 = 15 by norm_num, show 5 + 1 = 6 by norm_num] at h
  set g := Nat.gcd 6 (q + 1) with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hgle : g ≤ 6 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have h' : orderTwistedA 5 q * g = q ^ 15 * su6P q := by
    rw [← hq] at h
    rw [show 2 ^ (n * 15) = q ^ 15 by rw [hq, ← pow_mul]] at h
    simpa [su6P] using h
  have h1 : q ^ 15 * su6P q ≤ 6 * orderTwistedA 5 q := by
    rw [← h']
    calc orderTwistedA 5 q * g ≤ orderTwistedA 5 q * 6 := Nat.mul_le_mul_left _ hgle
      _ = 6 * orderTwistedA 5 q := Nat.mul_comm _ _
  have hP : q ^ 20 ≤ 8 * su6P q := pow_twenty_le_eight_su6P hq2
  calc q ^ 35 = q ^ 15 * q ^ 20 := by ring
    _ ≤ q ^ 15 * (8 * su6P q) := Nat.mul_le_mul_left _ hP
    _ = 8 * (q ^ 15 * su6P q) := by ring
    _ ≤ 8 * (6 * orderTwistedA 5 q) := Nat.mul_le_mul_left _ h1
    _ = 48 * orderTwistedA 5 q := by ring

private theorem te6P_le {q : ℕ} (hq : 1 ≤ q) : te6P q ≤ 4 * q ^ 42 := by
  unfold te6P
  have h9 : 1 ≤ q ^ 9 := Nat.one_le_pow _ _ hq
  have h5 : 1 ≤ q ^ 5 := Nat.one_le_pow _ _ hq
  have a12 : q ^ 12 - 1 ≤ q ^ 12 := Nat.sub_le _ _
  have a9 : q ^ 9 + 1 ≤ 2 * q ^ 9 := by omega
  have a8 : q ^ 8 - 1 ≤ q ^ 8 := Nat.sub_le _ _
  have a6 : q ^ 6 - 1 ≤ q ^ 6 := Nat.sub_le _ _
  have a5 : q ^ 5 + 1 ≤ 2 * q ^ 5 := by omega
  have a2 : q ^ 2 - 1 ≤ q ^ 2 := Nat.sub_le _ _
  calc (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1)
      = (((((q ^ 12 - 1) * (q ^ 9 + 1)) * (q ^ 8 - 1)) * (q ^ 6 - 1)) * (q ^ 5 + 1)) *
          (q ^ 2 - 1) := by ring
    _ ≤ (((((q ^ 12) * (2 * q ^ 9)) * q ^ 8) * q ^ 6) * (2 * q ^ 5)) * q ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
        (Nat.mul_le_mul a12 a9) a8) a6) a5) a2
    _ = 4 * q ^ 42 := by ring

theorem orderTwistedE6_le {q : ℕ} (hq : 1 ≤ q) :
    orderTwistedE6 q ≤ 4 * q ^ 78 := by
  rw [orderTwistedE6_eq]
  calc q ^ 36 * te6P q / Nat.gcd 3 (q + 1) ≤ q ^ 36 * te6P q := Nat.div_le_self _ _
    _ ≤ q ^ 36 * (4 * q ^ 42) := Nat.mul_le_mul_left _ (te6P_le hq)
    _ = 4 * q ^ 78 := by ring

theorem orderTwistedE6_two_pow_injective {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (h : orderTwistedE6 (2 ^ n) = orderTwistedE6 (2 ^ m)) : n = m := by
  obtain ⟨A, hAodd, hAn⟩ := two_part_orderTwistedE6 hn
  obtain ⟨B, hBodd, hBm⟩ := two_part_orderTwistedE6 hm
  rw [hAn, hBm] at h
  have he := (two_pow_mul_odd_inj hAodd hBodd h).1
  omega

theorem orderTwistedA_five_ne_orderTwistedE6 {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    orderTwistedA 5 (2 ^ n) ≠ orderTwistedE6 (2 ^ m) := by
  intro h
  obtain ⟨A, hAodd, hAn⟩ := CFSG.EvenSporadicStandard.Wong77.FinalArith.orderTwistedA_two_pow
    (N := 5) (k := n) (by norm_num) (by omega)
  rw [show n * (5 * (5 + 1) / 2) = 15 * n by omega] at hAn
  obtain ⟨B, hBodd, hBm⟩ := two_part_orderTwistedE6 hm
  rw [hAn, hBm] at h
  have he := (two_pow_mul_odd_inj hAodd hBodd h).1
  have h5n : 5 * n = 12 * m := by omega
  have h5m : 5 ∣ m := Nat.Coprime.dvd_of_dvd_mul_left (k := 5) (m := 12) (n := m)
    (by decide) (by rw [← h5n]; exact dvd_mul_right 5 n)
  obtain ⟨k, hk⟩ := h5m
  have hm5 : 5 ≤ m := by
    have hk1 : 1 ≤ k := by omega
    omega
  have hlow := pow_thirtyfive_le_orderTwistedA_five hn
  have hup := orderTwistedE6_le (q := 2 ^ m) (Nat.one_le_two_pow)
  have heq : orderTwistedE6 (2 ^ m) = orderTwistedA 5 (2 ^ n) := by
    rw [hBm, ← h, ← hAn]
  rw [heq] at hup
  have hmain : (2 ^ n) ^ 35 ≤ 48 * (4 * (2 ^ m) ^ 78) :=
    hlow.trans (Nat.mul_le_mul_left 48 hup)
  have hpow1 : (2 ^ n) ^ 35 = 2 ^ (84 * m) := by
    rw [← pow_mul]
    congr 1
    omega
  have hpow2 : (2 ^ m) ^ 78 = 2 ^ (78 * m) := by
    rw [← pow_mul, Nat.mul_comm m 78]
  rw [hpow1, hpow2] at hmain
  have hsplit : 2 ^ (84 * m) = 2 ^ (6 * m) * 2 ^ (78 * m) := by
    rw [← pow_add]
    congr 1
    ring
  rw [hsplit] at hmain
  have hpos : 0 < 2 ^ (78 * m) := by positivity
  have hmain' : 2 ^ (6 * m) * 2 ^ (78 * m) ≤ 192 * 2 ^ (78 * m) := by
    calc 2 ^ (6 * m) * 2 ^ (78 * m) ≤ 48 * (4 * 2 ^ (78 * m)) := hmain
      _ = 192 * 2 ^ (78 * m) := by ring
  have hle : 2 ^ (6 * m) ≤ 192 := Nat.le_of_mul_le_mul_right hmain' hpos
  have h30 : 2 ^ 30 ≤ 2 ^ (6 * m) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hgt : 192 < 2 ^ 30 := by norm_num
  omega

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
