module

public import CFSG.Open.Defs

public section

namespace CFSG.GH74.GLS.LU

open CFSG.Open

theorem ordBC_two_le (q : ℕ) : ordBC 2 q ≤ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  unfold ordBC
  have h1 : Finset.Icc 1 2 = {1, 2} := by decide
  rw [h1, Finset.prod_pair (by norm_num)]
  refine (Nat.div_le_self _ _).trans ?_
  norm_num

theorem ordA_three_ge (q : ℕ) :
    q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1))) / 4 ≤ ordA 3 q := by
  unfold ordA
  have h1 : Finset.Icc 2 4 = {2, 3, 4} := by decide
  rw [h1, Finset.prod_insert (by decide), Finset.prod_pair (by decide)]
  refine Nat.div_le_div_left ?_ (Nat.gcd_pos_of_pos_left _ (by norm_num))
  exact Nat.gcd_le_left _ (by norm_num)

theorem ordTwistedA_three_ge {q : ℕ} (hq : 5 ≤ q) :
    q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1))) / 4 ≤ ordTwistedA 3 q := by
  unfold ordTwistedA
  have h1 : Finset.Icc 2 4 = {2, 3, 4} := by decide
  rw [h1, Finset.prod_insert (by decide), Finset.prod_pair (by decide)]
  have e2 : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat = q ^ 2 - 1 := by
    have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub this]; ring
    rw [h, Int.toNat_natCast]
  have e3 : ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat = q ^ 3 + 1 := by
    have h : ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) := by
      push_cast; ring
    rw [h, Int.toNat_natCast]
  have e4 : ((q : ℤ) ^ 4 - (-1 : ℤ) ^ 4).toNat = q ^ 4 - 1 := by
    have : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
    have h : ((q : ℤ) ^ 4 - (-1 : ℤ) ^ 4) = ((q ^ 4 - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub this]; ring
    rw [h, Int.toNat_natCast]
  rw [e2, e3, e4]
  refine Nat.div_le_div_left ?_ (Nat.gcd_pos_of_pos_left _ (by norm_num))
  exact Nat.gcd_le_left _ (by norm_num)

theorem key_ineq_aux {q b : ℕ} (hq : 5 ≤ q) (hb : 8 ≤ b) :
    q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) < q ^ 6 * ((q ^ 2 - 1) * (b * (q ^ 4 - 1))) / 4 := by
  have ha : 1 ≤ q ^ 2 - 1 := by
    have : 25 ≤ q ^ 2 := by nlinarith
    omega
  have hc : 1 ≤ q ^ 4 - 1 := by
    have : 625 ≤ q ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℕ) ≤ 5) hq 4]
    omega
  have hq6 : q ^ 6 = q ^ 4 * q ^ 2 := by ring
  generalize q ^ 2 - 1 = a at *
  generalize q ^ 4 - 1 = c at *
  have e : q ^ 6 * (a * (b * c)) = q ^ 4 * (a * c) * (q ^ 2 * b) := by rw [hq6]; ring
  rw [e]
  have hx : 1 ≤ q ^ 4 * (a * c) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h25 : 25 ≤ q ^ 2 := by nlinarith
  have hd : 8 ≤ q ^ 2 * b := by nlinarith
  generalize q ^ 4 * (a * c) = x at *
  refine lt_of_lt_of_le (Nat.lt_succ_self x) ?_
  rw [Nat.succ_eq_add_one, Nat.le_div_iff_mul_le (by norm_num)]
  nlinarith

theorem ordBC_two_lt_ordA_three {q : ℕ} (hq : 5 ≤ q) : ordBC 2 q < ordA 3 q := by
  have hb : 8 ≤ q ^ 3 - 1 := by
    have : 125 ≤ q ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℕ) ≤ 5) hq 3]
    omega
  refine lt_of_le_of_lt (ordBC_two_le q) (lt_of_lt_of_le ?_ (ordA_three_ge q))
  exact key_ineq_aux hq hb

theorem ordBC_two_lt_ordTwistedA_three {q : ℕ} (hq : 5 ≤ q) :
    ordBC 2 q < ordTwistedA 3 q := by
  have hb : 8 ≤ q ^ 3 + 1 := by
    have : 125 ≤ q ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℕ) ≤ 5) hq 3]
    omega
  refine lt_of_le_of_lt (ordBC_two_le q) (lt_of_lt_of_le ?_ (ordTwistedA_three_ge hq))
  exact key_ineq_aux hq hb

end CFSG.GH74.GLS.LU
