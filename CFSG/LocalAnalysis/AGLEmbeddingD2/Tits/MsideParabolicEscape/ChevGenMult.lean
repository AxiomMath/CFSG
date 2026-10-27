module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeMult
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier CFSG.AGLEmbedding.ParabPrime

theorem centre_dvd_generic (hGA : CFSG.Open.GriessAllModelsStatement) {Y X : Type}
    [Group Y] [Finite Y] [Group X] (hY : CFSG.Open.IsQuasisimple Y)
    (e : Y ⧸ Subgroup.center Y ≃* X) {t : StatedLieTag} {n f : ℕ}
    (hL : CFSG.Models.LieModel X t n 2 f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpZ : p ∣ Nat.card (Subgroup.center Y)) :
    p ∣ (genericOrders t n 2 f).1 * (genericOrders t n 2 f).2 := by
  have h := hpZ.trans (card_center_dvd_of_griess hGA hY e hL)
  rw [generic, exceptional, Nat.card_prod, Nat.card_prod, card_multiplicative_zmod,
    card_multiplicative_zmod, card_multiplicative_zmod, card_multiplicative_zmod] at h
  have hexc : (0 < (exceptionalOrders t n 2 f).1 ∧ (exceptionalOrders t n 2 f).1 ≤ 4) ∧
      (0 < (exceptionalOrders t n 2 f).2 ∧ (exceptionalOrders t n 2 f).2 ≤ 4) := by
    unfold exceptionalOrders
    split <;> simp
  have hnd : ∀ m : ℕ, 0 < m → m ≤ 4 → ¬ p ∣ m := fun m hm hm4 hd => by
    have := Nat.le_of_dvd hm hd
    omega
  rcases hp.dvd_mul.1 h with h1 | h1
  · exact h1
  · exfalso
    rcases hp.dvd_mul.1 h1 with h2 | h2
    · exact hnd _ hexc.1.1 hexc.1.2 h2
    · exact hnd _ hexc.2.1 hexc.2.2 h2

theorem centre_dvd_psl (hGA : CFSG.Open.GriessAllModelsStatement) {Y X : Type}
    [Group Y] [Finite Y] [Group X] (hY : CFSG.Open.IsQuasisimple Y)
    (e : Y ⧸ Subgroup.center Y ≃* X) {n f : ℕ} (hL : CFSG.Models.LieModel X .PSL n 2 f)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpZ : p ∣ Nat.card (Subgroup.center Y)) :
    p ∣ 2 ^ f - 1 := by
  have hg := centre_dvd_generic hGA hY e hL hp hp5 hpZ
  have e1 : genericOrders .PSL n 2 f = (Nat.gcd n (2 ^ f - 1), 1) := by simp [genericOrders]
  rw [e1, mul_one] at hg
  exact hg.trans (Nat.gcd_dvd_right _ _)

theorem centre_dvd_psu (hGA : CFSG.Open.GriessAllModelsStatement) {Y X : Type}
    [Group Y] [Finite Y] [Group X] (hY : CFSG.Open.IsQuasisimple Y)
    (e : Y ⧸ Subgroup.center Y ≃* X) {n f : ℕ} (hL : CFSG.Models.LieModel X .PSU n 2 f)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpZ : p ∣ Nat.card (Subgroup.center Y)) :
    p ∣ 2 ^ f + 1 := by
  have hg := centre_dvd_generic hGA hY e hL hp hp5 hpZ
  have e1 : genericOrders .PSU n 2 f = (Nat.gcd n (2 ^ f + 1), 1) := by simp [genericOrders]
  rw [e1, mul_one] at hg
  exact hg.trans (Nat.gcd_dvd_right _ _)

theorem centre_false_of_tag (hGA : CFSG.Open.GriessAllModelsStatement) {Y X : Type}
    [Group Y] [Finite Y] [Group X] (hY : CFSG.Open.IsQuasisimple Y)
    (e : Y ⧸ Subgroup.center Y ≃* X) {t : StatedLieTag} {n f : ℕ}
    (ht : t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .G2)
    (hL : CFSG.Models.LieModel X t n 2 f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpZ : p ∣ Nat.card (Subgroup.center Y)) : False := by
  have hg := centre_dvd_generic hGA hY e hL hp hp5 hpZ
  have hnd : ∀ m : ℕ, 0 < m → m ≤ 4 → ¬ p ∣ m := fun m hm hm4 hd => by
    have := Nat.le_of_dvd hm hd
    omega
  have hq2 : Even (2 ^ f) := by
    have hf : f ≠ 0 := by
      rintro rfl
      have := hL.1.2.1
      omega
    exact Nat.even_pow.2 ⟨even_two, hf⟩
  rcases ht with rfl | rfl | rfl | rfl
  · have e1 : genericOrders .PSp n 2 f = (Nat.gcd 2 (2 ^ f - 1), 1) := by simp [genericOrders]
    rw [e1, mul_one] at hg
    exact hnd 2 (by norm_num) (by norm_num) (hg.trans (Nat.gcd_dvd_left _ _))
  · have e1 : genericOrders .POmegaPlus n 2 f = (1, 1) := by simp [genericOrders, hq2]
    rw [e1] at hg
    exact hp.one_lt.ne' (Nat.dvd_one.1 (by simpa using hg))
  · have e1 : genericOrders .POmegaMinus n 2 f = (Nat.gcd 4 ((2 ^ f) ^ n + 1), 1) := by
      simp [genericOrders]
    rw [e1, mul_one] at hg
    exact hnd 4 (by norm_num) (by norm_num) (hg.trans (Nat.gcd_dvd_left _ _))
  · have e1 : genericOrders .G2 n 2 f = (1, 1) := by simp [genericOrders]
    rw [e1] at hg
    exact hp.one_lt.ne' (Nat.dvd_one.1 (by simpa using hg))

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen
