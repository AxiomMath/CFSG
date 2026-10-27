module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Comp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof (lieOrderCofactor lieOrderNumerator_eq)
open CFSG.SeitzReduction.CrossChar
open Finset
open CFSG.ComponentClassification.CatLeafProof (lieOrderDivisor_ne_zero not_dvd_lieOrderDivisor
  lieOrderCofactor_coprime)

section TD4

open scoped Nat

theorem M_lt_pow {t : StatedLieTag} {n f M : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f)) :
    M < (2 ^ f) ^ (lieSylowExponent t n + cofE t n) := by
  have hD : 1 ≤ lieOrderDivisor t n (2 ^ f) :=
    Nat.one_le_iff_ne_zero.mpr (lieOrderDivisor_ne_zero hadm)
  rw [lieOrderNumerator_eq hadm] at hM
  have hq : 1 ≤ 2 ^ f := Nat.one_le_pow _ _ (by norm_num)
  calc M ≤ M * lieOrderDivisor t n (2 ^ f) := Nat.le_mul_of_pos_right M hD
    _ = (2 ^ f) ^ lieSylowExponent t n * lieOrderCofactor t n (2 ^ f) := hM
    _ < (2 ^ f) ^ lieSylowExponent t n * (2 ^ f) ^ cofE t n :=
        Nat.mul_lt_mul_of_pos_left (cof_lt_pow hadm) (by positivity)
    _ = (2 ^ f) ^ (lieSylowExponent t n + cofE t n) := (pow_add _ _ _).symm

theorem sylowExp_TD4 : lieSylowExponent .trialityD4 0 = 12 := by simp [lieSylowExponent]

theorem order_TD4 {e M : ℕ}
    (hM : M * lieOrderDivisor .trialityD4 0 (2 ^ e) = lieOrderNumerator .trialityD4 0 (2 ^ e)) :
    M = (2 ^ e) ^ 12 * ((2 ^ e) ^ 8 + (2 ^ e) ^ 4 + 1) * ((2 ^ e) ^ 6 - 1) * ((2 ^ e) ^ 2 - 1) := by
  have hD : lieOrderDivisor .trialityD4 0 (2 ^ e) = 1 := rfl
  rw [hD, mul_one] at hM
  rw [hM]
  rfl

theorem td4_ge {e M : ℕ} (he : 2 ≤ e)
    (hM : M * lieOrderDivisor .trialityD4 0 (2 ^ e) = lieOrderNumerator .trialityD4 0 (2 ^ e)) :
    (2 ^ e) ^ 28 ≤ 2 * M := by
  rw [order_TD4 hM]
  have h4 : 4 ≤ 2 ^ e := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  generalize 2 ^ e = Q at h4 ⊢
  have h6 : 1 ≤ Q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hYZ : Q ^ 8 ≤ 2 * ((Q ^ 6 - 1) * (Q ^ 2 - 1)) := by
    zify [h6, h2]
    have hu : (16 : ℤ) ≤ (Q : ℤ) ^ 2 := by nlinarith
    have e6 : (Q : ℤ) ^ 6 = ((Q : ℤ) ^ 2) ^ 3 := by ring
    have e8 : (Q : ℤ) ^ 8 = ((Q : ℤ) ^ 2) ^ 4 := by ring
    rw [e6, e8]
    generalize (Q : ℤ) ^ 2 = u at hu ⊢
    nlinarith [mul_nonneg (mul_nonneg (show (0 : ℤ) ≤ u by linarith) (show (0 : ℤ) ≤ u by linarith))
      (show (0 : ℤ) ≤ u by linarith), mul_nonneg (show (0 : ℤ) ≤ u ^ 3 by positivity)
      (show (0 : ℤ) ≤ u - 16 by linarith)]
  have hX : Q ^ 8 ≤ Q ^ 8 + Q ^ 4 + 1 := by omega
  calc Q ^ 28 = Q ^ 12 * Q ^ 8 * Q ^ 8 := by ring
    _ ≤ Q ^ 12 * (Q ^ 8 + Q ^ 4 + 1) * (2 * ((Q ^ 6 - 1) * (Q ^ 2 - 1))) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hX) hYZ
    _ = 2 * (Q ^ 12 * (Q ^ 8 + Q ^ 4 + 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1)) := by ring

theorem gcd_four_odd {x : ℕ} (hx : Odd x) : Nat.gcd 4 x = 1 := by
  have : Nat.Coprime (2 ^ 2) x := (Nat.coprime_two_left.mpr hx).pow_left 2
  simpa using this

theorem D4_ne_TD4 {e M : ℕ} (he : 2 ≤ e)
    (hM : M * lieOrderDivisor .POmegaPlus 4 (2 ^ e) = lieOrderNumerator .POmegaPlus 4 (2 ^ e))
    (hM' : M * lieOrderDivisor .trialityD4 0 (2 ^ e) = lieOrderNumerator .trialityD4 0 (2 ^ e)) :
    False := by
  have h4 : 4 ≤ 2 ^ e := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hev : Even (2 ^ e) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hD : lieOrderDivisor .POmegaPlus 4 (2 ^ e) = 1 := by
    show Nat.gcd 4 ((2 ^ e) ^ 4 - 1) = 1
    apply gcd_four_odd
    have : Even ((2 ^ e) ^ 4) := Nat.even_pow.mpr ⟨hev, by norm_num⟩
    exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by omega)) this odd_one
  rw [hD, mul_one] at hM
  have hM2 := order_TD4 hM'
  generalize 2 ^ e = Q at h4 hM hM2
  have e1 : lieOrderNumerator .POmegaPlus 4 Q =
      Q ^ 12 * ((Q ^ 4 - 1) * ((Q ^ 2 - 1) * (Q ^ 4 - 1) * (Q ^ 6 - 1))) := by
    have : (∏ i ∈ Finset.Icc 1 3, (Q ^ (2 * i) - 1)) = (Q ^ 2 - 1) * (Q ^ 4 - 1) * (Q ^ 6 - 1) := by
      simp [Finset.prod_Icc_succ_top]
    simp only [lieOrderNumerator]
    norm_num [this, mul_assoc]
  rw [e1] at hM
  have hQ12 : 0 < Q ^ 12 := by positivity
  have key : Q ^ 12 * ((Q ^ 4 - 1) * ((Q ^ 2 - 1) * (Q ^ 4 - 1) * (Q ^ 6 - 1))) =
      Q ^ 12 * (((Q ^ 8 + Q ^ 4 + 1) * (Q ^ 6 - 1)) * (Q ^ 2 - 1)) := by
    rw [← hM]
    rw [hM2]
    ring
  have key' := Nat.eq_of_mul_eq_mul_left hQ12 key
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h4' : 1 ≤ Q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h6 : 1 ≤ Q ^ 6 := Nat.one_le_pow _ _ (by omega)
  zify [h2, h4', h6] at key'
  have hQ : (4 : ℤ) ≤ Q := by exact_mod_cast h4
  have hpos : (0 : ℤ) < (Q : ℤ) ^ 4 * 3 * (((Q : ℤ) ^ 2 - 1) * ((Q : ℤ) ^ 6 - 1)) := by
    have a1 : (1 : ℤ) < (Q : ℤ) ^ 2 := by nlinarith
    have a2 : (1 : ℤ) < (Q : ℤ) ^ 6 := by nlinarith [pow_pos (show (0 : ℤ) < Q by omega) 4]
    have a3 : (0 : ℤ) < (Q : ℤ) ^ 4 := by positivity
    have := mul_pos (sub_pos.mpr a1) (sub_pos.mpr a2)
    positivity
  have : (Q : ℤ) ^ 4 * 3 * (((Q : ℤ) ^ 2 - 1) * ((Q : ℤ) ^ 6 - 1)) = 0 := by
    linear_combination (-1 : ℤ) * key'
  linarith

theorem twD4_ne_TD4 {e M : ℕ} (he : 2 ≤ e)
    (hM : M * lieOrderDivisor .POmegaMinus 4 (2 ^ e) = lieOrderNumerator .POmegaMinus 4 (2 ^ e))
    (hM' : M * lieOrderDivisor .trialityD4 0 (2 ^ e) = lieOrderNumerator .trialityD4 0 (2 ^ e)) :
    False := by
  have h4 : 4 ≤ 2 ^ e := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hev : Even (2 ^ e) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hD : lieOrderDivisor .POmegaMinus 4 (2 ^ e) = 1 := by
    show Nat.gcd 4 ((2 ^ e) ^ 4 + 1) = 1
    apply gcd_four_odd
    have : Even ((2 ^ e) ^ 4) := Nat.even_pow.mpr ⟨hev, by norm_num⟩
    exact this.add_one
  rw [hD, mul_one] at hM
  have hM2 := order_TD4 hM'
  generalize 2 ^ e = Q at h4 hM hM2
  have e1 : lieOrderNumerator .POmegaMinus 4 Q =
      Q ^ 12 * ((Q ^ 4 + 1) * ((Q ^ 2 - 1) * (Q ^ 4 - 1) * (Q ^ 6 - 1))) := by
    have : (∏ i ∈ Finset.Icc 1 3, (Q ^ (2 * i) - 1)) = (Q ^ 2 - 1) * (Q ^ 4 - 1) * (Q ^ 6 - 1) := by
      simp [Finset.prod_Icc_succ_top]
    simp only [lieOrderNumerator]
    norm_num [this, mul_assoc]
  rw [e1] at hM
  have hQ12 : 0 < Q ^ 12 := by positivity
  have key : Q ^ 12 * ((Q ^ 4 + 1) * ((Q ^ 2 - 1) * (Q ^ 4 - 1) * (Q ^ 6 - 1))) =
      Q ^ 12 * (((Q ^ 8 + Q ^ 4 + 1) * (Q ^ 6 - 1)) * (Q ^ 2 - 1)) := by
    rw [← hM]
    rw [hM2]
    ring
  have key' := Nat.eq_of_mul_eq_mul_left hQ12 key
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h4' : 1 ≤ Q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h6 : 1 ≤ Q ^ 6 := Nat.one_le_pow _ _ (by omega)
  zify [h2, h4', h6] at key'
  have hQ : (4 : ℤ) ≤ Q := by exact_mod_cast h4
  have hpos : (0 : ℤ) < ((Q : ℤ) ^ 4 + 2) * (((Q : ℤ) ^ 2 - 1) * ((Q : ℤ) ^ 6 - 1)) := by
    have a1 : (1 : ℤ) < (Q : ℤ) ^ 2 := by nlinarith
    have a2 : (1 : ℤ) < (Q : ℤ) ^ 6 := by nlinarith [pow_pos (show (0 : ℤ) < Q by omega) 4]
    have a3 : (0 : ℤ) < (Q : ℤ) ^ 4 + 2 := by positivity
    exact mul_pos a3 (mul_pos (sub_pos.mpr a1) (sub_pos.mpr a2))
  have : ((Q : ℤ) ^ 4 + 2) * (((Q : ℤ) ^ 2 - 1) * ((Q : ℤ) ^ 6 - 1)) = 0 := by
    linear_combination (-1 : ℤ) * key'
  linarith

theorem td4_excl {t : StatedLieTag} {n f e M : ℕ} (he : 2 ≤ e) (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hM' : M * lieOrderDivisor .trialityD4 0 (2 ^ e) = lieOrderNumerator .trialityD4 0 (2 ^ e))
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .F4 ∨
      t = .twistedE6) : False := by
  have hadm' : StatedLieAdmissible .trialityD4 0 2 e := ⟨Nat.prime_two, by omega, rfl⟩
  have hv := v2_eq_of_two hadm hM hadm' hM'
  rw [sylowExp_TD4] at hv
  by_cases hD4 : (t = .POmegaPlus ∨ t = .POmegaMinus) ∧ n = 4
  · obtain ⟨hpm, rfl⟩ := hD4
    have hfe : f = e := by
      rcases hpm with rfl | rfl <;> simp [lieSylowExponent] at hv <;> omega
    subst hfe
    rcases hpm with rfl | rfl
    · exact D4_ne_TD4 he hM hM'
    · exact twD4_ne_TD4 he hM hM'
  · have hlow := td4_ge he hM'
    have hup := M_lt_pow hadm hM
    have hf : 1 ≤ f := hadm.2.1
    have hE : 3 * cofE t n < 4 * lieSylowExponent t n := by
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨-, -, hn⟩ := hadm
        have h5 : 5 ≤ n := by
          by_contra hlt
          exact hD4 ⟨Or.inl rfl, by omega⟩
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
        simp only [cofE, lieSylowExponent, show k + 5 - 1 = k + 4 by omega]
        nlinarith
      · obtain ⟨-, -, hn⟩ := hadm
        have h5 : 5 ≤ n := by
          by_contra hlt
          exact hD4 ⟨Or.inr rfl, by omega⟩
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
        simp only [cofE, lieSylowExponent, show k + 5 - 1 = k + 4 by omega]
        nlinarith
      all_goals simp [cofE, lieSylowExponent]
    have hlow' : 2 ^ (e * 28) ≤ 2 * M := by
      rw [pow_mul]; exact hlow
    have hup' : 2 * M < 2 ^ (f * (lieSylowExponent t n + cofE t n) + 1) := by
      have := Nat.mul_lt_mul_of_pos_left hup (show 0 < 2 by norm_num)
      calc 2 * M < 2 * (2 ^ f) ^ (lieSylowExponent t n + cofE t n) := this
        _ = 2 ^ (f * (lieSylowExponent t n + cofE t n) + 1) := by
          rw [← pow_mul, pow_succ]; ring
    have h28 : e * 28 < f * (lieSylowExponent t n + cofE t n) + 1 :=
      (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (lt_of_le_of_lt hlow' hup')
    have h28' : e * 28 ≤ f * (lieSylowExponent t n + cofE t n) := by omega
    have hprod : (3 * cofE t n + 1) * f ≤ 4 * lieSylowExponent t n * f :=
      Nat.mul_le_mul_right f (by omega)
    nlinarith

end TD4

end CFSG.LocalAnalysis.GLTheoremA.HDesc
