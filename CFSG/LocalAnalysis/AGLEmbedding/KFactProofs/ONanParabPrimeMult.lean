module

public import CFSG.GH74.Generic.GKFCover
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.AGLEmbedding.ParabPrime

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

theorem card_center_dvd_of_griess (hGA : CFSG.Open.GriessAllModelsStatement) {Y X : Type}
    [Group Y] [Finite Y] [Group X] (hY : CFSG.Open.IsQuasisimple Y)
    (e : Y ⧸ Subgroup.center Y ≃* X) {t : StatedLieTag} {n p f : ℕ}
    (hL : CFSG.Models.LieModel X t n p f) :
    Nat.card (Subgroup.center Y) ∣
      Nat.card (generic t n p f) * Nat.card (exceptional t n p f) := by
  have hnonab : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a := by
    have : Group.IsPerfect Y := ⟨hY.1⟩
    have : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hY.2
    have hnoncomm := Group.IsPerfect.not_isMulCommutative (Y ⧸ Subgroup.center Y)
    simpa only [isMulCommutative_iff, not_forall] using hnoncomm
  have hY' : CFSG.IsQuasisimple Y := ⟨⟨hY.1⟩, hY.2, hnonab⟩
  have h1 := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hY' e
  obtain ⟨-, ⟨eq⟩⟩ := hGA X t n p f hL
  have h2 : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier X) =
      Nat.card (generic t n p f) * Nat.card (exceptional t n p f) := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (((CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).symm.trans
      eq).toEquiv)
  rwa [h2] at h1

theorem card_multiplicative_zmod (a : ℕ) : Nat.card (Multiplicative (ZMod a)) = a := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod a) ≃ ZMod a)]
  exact Nat.card_zmod a

theorem sub_one_dvd_and_add_one_dvd (q : ℕ) (hq : 1 ≤ q) :
    q - 1 ∣ q ^ 2 - 1 ∧ q + 1 ∣ q ^ 2 - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  have h : (k + 1) ^ 2 - 1 = k * (k + 2) := by
    rw [Nat.sub_eq_of_eq_add]
    ring
  rw [h]
  exact ⟨⟨k + 2, by simp⟩, ⟨k, by ring⟩⟩

theorem dvd_sq_sub_one_of_dvd_card_center (hGA : CFSG.Open.GriessAllModelsStatement)
    {Y X : Type} [Group Y] [Finite Y] [Group X] (hY : CFSG.Open.IsQuasisimple Y)
    (e : Y ⧸ Subgroup.center Y ≃* X) {t : StatedLieTag} {n f : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .G2)
    (hf : 1 ≤ f) (hL : CFSG.Models.LieModel X t n 2 f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpZ : p ∣ Nat.card (Subgroup.center Y)) : p ∣ (2 ^ f) ^ 2 - 1 := by
  have h := hpZ.trans (card_center_dvd_of_griess hGA hY e hL)
  rw [generic, exceptional, Nat.card_prod, Nat.card_prod, card_multiplicative_zmod,
    card_multiplicative_zmod, card_multiplicative_zmod, card_multiplicative_zmod] at h
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  obtain ⟨hq1d, hq2d⟩ := sub_one_dvd_and_add_one_dvd (2 ^ f) hq1
  have hexc : (0 < (exceptionalOrders t n 2 f).1 ∧ (exceptionalOrders t n 2 f).1 ≤ 4) ∧
      (0 < (exceptionalOrders t n 2 f).2 ∧ (exceptionalOrders t n 2 f).2 ≤ 4) := by
    unfold exceptionalOrders
    split <;> simp
  have hnd : ∀ m : ℕ, 0 < m → m ≤ 4 → ¬ p ∣ m := fun m hm hm4 hd => by
    have := Nat.le_of_dvd hm hd
    omega
  have hg : p ∣ (genericOrders t n 2 f).1 * (genericOrders t n 2 f).2 := by
    rcases hp.dvd_mul.1 h with h1 | h1
    · exact h1
    · exfalso
      rcases hp.dvd_mul.1 h1 with h2 | h2
      · exact hnd _ hexc.1.1 hexc.1.2 h2
      · exact hnd _ hexc.2.1 hexc.2.2 h2
  have hq2 : Even (2 ^ f) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · have e1 : genericOrders .PSL n 2 f = (Nat.gcd n (2 ^ f - 1), 1) := by simp [genericOrders]
    rw [e1, mul_one] at hg
    exact (hg.trans (Nat.gcd_dvd_right _ _)).trans hq1d
  · have e1 : genericOrders .PSU n 2 f = (Nat.gcd n (2 ^ f + 1), 1) := by simp [genericOrders]
    rw [e1, mul_one] at hg
    exact (hg.trans (Nat.gcd_dvd_right _ _)).trans hq2d
  · have e1 : genericOrders .PSp n 2 f = (Nat.gcd 2 (2 ^ f - 1), 1) := by simp [genericOrders]
    rw [e1, mul_one] at hg
    exfalso
    exact hnd 2 (by norm_num) (by norm_num) (hg.trans (Nat.gcd_dvd_left _ _))
  · have e1 : genericOrders .POmegaPlus n 2 f = (1, 1) := by simp [genericOrders, hq2]
    rw [e1] at hg
    exfalso
    exact hp.one_lt.ne' (Nat.dvd_one.1 (by simpa using hg))
  · have e1 : genericOrders .POmegaMinus n 2 f = (Nat.gcd 4 ((2 ^ f) ^ n + 1), 1) := by
      simp [genericOrders]
    rw [e1, mul_one] at hg
    exfalso
    exact hnd 4 (by norm_num) (by norm_num) (hg.trans (Nat.gcd_dvd_left _ _))
  · have e1 : genericOrders .G2 n 2 f = (1, 1) := by simp [genericOrders]
    rw [e1] at hg
    exfalso
    exact hp.one_lt.ne' (Nat.dvd_one.1 (by simpa using hg))

end CFSG.AGLEmbedding.ParabPrime
