module

public import CFSG.Timmesfeld.Orders.ClassicalUnitaryThree

public section

namespace CFSG.Open.StatedAPI

open CFSG.Assembly.LowTwoRank

theorem card_statedProj_statedSL_two_of_odd {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) :
    Nat.card (StatedProj (StatedSL 2 F)) = Nat.card F * (Nat.card F ^ 2 - 1) / 2 := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num)]
  have hg : Nat.gcd 2 (Nat.card F - 1) = 2 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, Nat.add_sub_cancel]
    exact Nat.gcd_eq_left (dvd_mul_right 2 k)
  norm_num [hg]

theorem card_statedProj_statedSU_three_of_prime {K : Type} [Field K] {p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ 2) :
    Nat.card (StatedProj (StatedSU 3 p K)) =
      p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) / Nat.gcd 3 (p + 1) := by
  have hK' : Nat.card K = (p ^ 1) ^ 2 := by rw [hK, pow_one]
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU hp (le_refl 1) hK'
    (by norm_num : 2 ≤ 3)
  simp only [pow_one] at h
  rw [h, show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  have hq : 1 ≤ p := hp.one_lt.le
  have h2 : (((p : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat = p ^ 2 - 1 := by
    have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
    rw [show ((p : ℕ) : ℤ) ^ 2 - (-1) ^ 2 = ((p ^ 2 - 1 : ℕ) : ℤ) by
      push_cast [Nat.cast_sub this]; ring]
    exact Int.toNat_natCast _
  have h3 : (((p : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat = p ^ 3 + 1 := by
    rw [show ((p : ℕ) : ℤ) ^ 3 - (-1) ^ 3 = ((p ^ 3 + 1 : ℕ) : ℤ) by push_cast; ring]
    exact Int.toNat_natCast _
  rw [h2, h3]

theorem card_mul_gcd_of_statedClassicalModel_psu_three {X : Type} [Group X] {p e : ℕ}
    (h : StatedClassicalModel X .PSU 3 p e) :
    Nat.card X * Nat.gcd 3 (p ^ e + 1) = (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)) := by
  obtain ⟨⟨hp, he, -⟩, K, _, _, hK, ⟨φ⟩⟩ := h
  rw [Nat.card_congr φ.toEquiv]
  exact CFSG.Timmesfeld.ClassicalOrders.card_psu_three_mul_gcd hp he hK

end CFSG.Open.StatedAPI
