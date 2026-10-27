module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTable

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open

theorem orderOf_cast_eq_one_iff {m r : ℕ} (hm : 1 ≤ m) :
    orderOf (m : ZMod r) = 1 ↔ r ∣ m - 1 := by
  rw [orderOf_eq_one_iff, ← CharP.cast_eq_zero_iff (ZMod r) r (m - 1), Nat.cast_sub hm,
    Nat.cast_one, sub_eq_zero]

theorem eP_eq_one_iff {Q r : ℕ} (hQ : 1 ≤ Q) : eP Q r = 1 ↔ r ∣ Q - 1 :=
  orderOf_cast_eq_one_iff hQ

theorem eM_eq_one_iff {Q r : ℕ} : eM Q r = 1 ↔ r ∣ Q + 1 := by
  unfold eM
  rw [orderOf_eq_one_iff, ← CharP.cast_eq_zero_iff (ZMod r) r (Q + 1), Nat.cast_add, Nat.cast_one,
    neg_eq_iff_add_eq_zero]

theorem eS_eq_one_iff {Q r : ℕ} (hQ : 1 ≤ Q) : eS Q r = 1 ↔ r ∣ Q ^ 2 - 1 := by
  unfold eS
  rw [← Nat.cast_pow]
  exact orderOf_cast_eq_one_iff (Nat.one_le_pow _ _ (by omega))

theorem eS_eq_eP_div_gcd {Q r : ℕ} : eS Q r = eP Q r / Nat.gcd (eP Q r) 2 :=
  orderOf_pow' (Q : ZMod r) two_ne_zero

theorem eP_two_pow_three (n : ℕ) : eP (2 ^ n) 3 = if Even n then 1 else 2 := by
  have hc : ((2 ^ n : ℕ) : ZMod 3) = (2 : ZMod 3) ^ n := by norm_num
  have hev : ∀ k : ℕ, (2 : ZMod 3) ^ (2 * k) = 1 := fun k => by
    rw [pow_mul, show (2 : ZMod 3) ^ 2 = 1 by decide, one_pow]
  unfold eP
  rw [hc]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [if_pos (even_two_mul k), hev k, orderOf_one]
  · rw [if_neg (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one k)), pow_succ, hev k, one_mul]
    exact orderOf_eq_prime (by decide) (by decide)

theorem eM_two_pow_three (n : ℕ) : eM (2 ^ n) 3 = if Even n then 2 else 1 := by
  have hc : ((2 ^ n : ℕ) : ZMod 3) = (2 : ZMod 3) ^ n := by norm_num
  have hev : ∀ k : ℕ, (2 : ZMod 3) ^ (2 * k) = 1 := fun k => by
    rw [pow_mul, show (2 : ZMod 3) ^ 2 = 1 by decide, one_pow]
  unfold eM
  rw [hc]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [if_pos (even_two_mul k), hev k]
    exact orderOf_eq_prime (by decide) (by decide)
  · rw [if_neg (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one k)), pow_succ, hev k, one_mul]
    exact orderOf_eq_one_iff.mpr (by decide)

theorem eS_two_pow_three (n : ℕ) : eS (2 ^ n) 3 = 1 := by
  have hc : ((2 ^ n : ℕ) : ZMod 3) = (2 : ZMod 3) ^ n := by norm_num
  unfold eS
  rw [orderOf_eq_one_iff, hc, ← pow_mul, mul_comm, pow_mul, show (2 : ZMod 3) ^ 2 = 1 by decide,
    one_pow]

theorem eP_4_3 : eP 4 3 = 1 :=
  (eP_eq_one_iff (Q := 4) (r := 3) (by norm_num)).mpr (by norm_num)

theorem eM_4_5 : eM 4 5 = 1 :=
  eM_eq_one_iff.mpr (by norm_num)

theorem eM_2_3 : eM 2 3 = 1 :=
  eM_eq_one_iff.mpr (by norm_num)

theorem padicValNat_three_three : padicValNat 3 3 = 1 :=
  padicValNat_self

theorem padicValNat_three_six : padicValNat 3 6 = 1 := by
  have h := padicValNat.mul (p := 3) (a := 3) (b := 2) (by norm_num) (by norm_num)
  rw [padicValNat_three_three, padicValNat.eq_zero_of_not_dvd (p := 3) (n := 2) (by norm_num)] at h
  simpa using h

theorem rkLin_SL6_4_r3_z1 : rkLin 6 true 4 3 1 = 4 := by
  norm_num [rkLin, eP_4_3, padicValNat_three_three, padicValNat_three_six]

end CFSG.LocalAnalysis.RankThreeUC.S15
