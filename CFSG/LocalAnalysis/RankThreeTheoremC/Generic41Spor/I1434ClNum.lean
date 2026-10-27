module

public import CFSG.Assembly.OrderReductions.LinearOrders

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl

theorem eq_two_four_five_of_order (q m : ℕ) (hq : 2 ≤ q) (hm : 2 ≤ m)
    (h : q ^ (m * (m - 1) / 2) * ∏ i ∈ Finset.Icc 2 m, (q ^ i - 1) = 60 * m.gcd (q - 1)) :
    m = 2 ∧ (q = 4 ∨ q = 5) := by
  have hcop : Nat.Coprime (q ^ (m * (m - 1) / 2)) (m.gcd (q - 1)) := by
    refine Nat.Coprime.pow_left _ ?_
    refine Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right m (q - 1)) ?_
    have : Nat.Coprime (q - 1 + 1) (q - 1) := by simp
    rwa [Nat.sub_add_cancel (by omega)] at this
  have hdvd : q ^ (m * (m - 1) / 2) ∣ 60 := by
    refine hcop.dvd_of_dvd_mul_right ?_
    rw [← h]
    exact Dvd.intro _ rfl
  have hle : q ^ (m * (m - 1) / 2) ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd
  have hm4 : m ≤ 4 := by
    by_contra hcon
    have h5 : 5 * 4 ≤ m * (m - 1) := Nat.mul_le_mul (by omega : 5 ≤ m) (by omega : 4 ≤ m - 1)
    have h10 : 10 ≤ m * (m - 1) / 2 := by omega
    have : 2 ^ 10 ≤ q ^ (m * (m - 1) / 2) :=
      (Nat.pow_le_pow_left hq 10).trans (Nat.pow_le_pow_right (by omega) h10)
    omega
  interval_cases m
  · simp at h
    have hg : (2 : ℕ).gcd (q - 1) ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have hq9 : q ≤ 9 := by
      by_contra hcon
      have h10 : 10 ≤ q := by omega
      have : q * (q ^ 2 - 1) ≥ 10 * (10 ^ 2 - 1) := by
        apply Nat.mul_le_mul h10
        exact Nat.sub_le_sub_right (Nat.pow_le_pow_left h10 2) 1
      omega
    interval_cases q <;> simp_all
  · have hI : Finset.Icc 2 3 = {2, 3} := by decide
    simp [hI] at h hle
    have hq7 : q ≤ 3 := by
      by_contra hcon
      have h4 : 4 ≤ q := by omega
      have : 4 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left h4 3
      omega
    interval_cases q <;> simp_all
  · have hI : Finset.Icc 2 4 = {2, 3, 4} := by decide
    simp [hI] at h hle
    have hq2 : q ≤ 1 := by
      by_contra hcon
      have h2 : 2 ≤ q := by omega
      have : 2 ^ 6 ≤ q ^ 6 := Nat.pow_le_pow_left h2 6
      omega
    omega

theorem sl_a5 {E : Type} [Field E] [Finite E] {m : ℕ} (hm : 2 ≤ m)
    (h : Nat.card (Matrix.SpecialLinearGroup (Fin m) E ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E)) = 60) :
    m = 2 ∧ (Nat.card E = 4 ∨ Nat.card E = 5) := by
  have hq : 2 ≤ Nat.card E := Nat.succ_le_of_lt Finite.one_lt_card
  have hsl := CFSG.OrderReductions.LinearOrders.card_specialLinear E m (by omega)
  have hz := CFSG.OrderReductions.LinearOrders.card_specialLinear_center E m (by omega)
  have hmul := (Subgroup.center
    (Matrix.SpecialLinearGroup (Fin m) E)).card_eq_card_quotient_mul_card_subgroup
  rw [h, hz, hsl] at hmul
  exact eq_two_four_five_of_order (Nat.card E) m hq hm hmul

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl
