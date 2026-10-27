module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2TD4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof (lieOrderCofactor lieOrderNumerator_eq)
open CFSG.SeitzReduction.CrossChar
open Finset
open CFSG.ComponentClassification.CatLeafProof (lieOrderDivisor_ne_zero not_dvd_lieOrderDivisor
  lieOrderCofactor_coprime)

section TD4B

open scoped Nat

theorem td4_excl_crude {t : StatedLieTag} {n f e M : ℕ} (he : 2 ≤ e)
    (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hM' : M * lieOrderDivisor .trialityD4 0 (2 ^ e) = lieOrderNumerator .trialityD4 0 (2 ^ e))
    (hE : 3 * cofE t n < 4 * lieSylowExponent t n) : False := by
  have hadm' : StatedLieAdmissible .trialityD4 0 2 e := ⟨Nat.prime_two, by omega, rfl⟩
  have hv := v2_eq_of_two hadm hM hadm' hM'
  rw [sylowExp_TD4] at hv
  have hlow := td4_ge he hM'
  have hup := M_lt_pow hadm hM
  have hf : 1 ≤ f := hadm.2.1
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

theorem order_Sp {n f M : ℕ} (hf : 1 ≤ f)
    (hM : M * lieOrderDivisor .PSp n (2 ^ f) = lieOrderNumerator .PSp n (2 ^ f)) :
    M = (2 ^ f) ^ (n ^ 2) * ∏ i ∈ Finset.Icc 1 n, ((2 ^ f) ^ (2 * i) - 1) := by
  have hD : lieOrderDivisor .PSp n (2 ^ f) = 1 := by
    show Nat.gcd 2 (2 ^ f - 1) = 1
    have hodd : Odd (2 ^ f - 1) := by
      have h2 : Even (2 ^ f) := Nat.even_pow.mpr ⟨even_two, by omega⟩
      exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num)) h2 odd_one
    exact Nat.coprime_two_left.mpr hodd
  rw [hD, mul_one] at hM
  exact hM


theorem sp2_ne_TD4 {e M : ℕ} (he : 2 ≤ e)
    (hM : M * lieOrderDivisor .PSp 2 (2 ^ (3 * e)) = lieOrderNumerator .PSp 2 (2 ^ (3 * e)))
    (hM' : M * lieOrderDivisor .trialityD4 0 (2 ^ e) = lieOrderNumerator .trialityD4 0 (2 ^ e)) :
    False := by
  have h4 : 4 ≤ 2 ^ e := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hM1 := order_Sp (by omega) hM
  have hM2 := order_TD4 hM'
  rw [pow_mul'] at hM1
  generalize 2 ^ e = q at h4 hM1 hM2
  have e1 : M = q ^ 12 * ((q ^ 6 - 1) * (q ^ 12 - 1)) := by
    rw [hM1]
    have hp : (∏ i ∈ Finset.Icc 1 2, ((q ^ 3) ^ (2 * i) - 1)) =
        ((q ^ 3) ^ 2 - 1) * ((q ^ 3) ^ 4 - 1) := by
      simp [Finset.prod_Icc_succ_top]
    rw [hp]
    have a1 : (q ^ 3) ^ 2 = q ^ 6 := by ring
    have a2 : (q ^ 3) ^ 4 = q ^ 12 := by ring
    have a3 : (q ^ 3) ^ (2 ^ 2) = q ^ 12 := by ring
    rw [a1, a2, a3]
  have key : q ^ 12 * ((q ^ 6 - 1) * (q ^ 12 - 1)) =
      q ^ 12 * ((q ^ 6 - 1) * ((q ^ 8 + q ^ 4 + 1) * (q ^ 2 - 1))) := by
    rw [← e1, hM2]
    ring
  have hq12 : 0 < q ^ 12 := by positivity
  have hq6 : 1 < q ^ 6 := by
    calc 1 < 4 ^ 6 := by norm_num
      _ ≤ q ^ 6 := Nat.pow_le_pow_left h4 6
  have key1 := Nat.eq_of_mul_eq_mul_left hq12 key
  have key2 := Nat.eq_of_mul_eq_mul_left (Nat.sub_pos_of_lt hq6) key1
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h12 : 1 ≤ q ^ 12 := Nat.one_le_pow _ _ (by omega)
  zify [h2, h12] at key2
  have hQ : (4 : ℤ) ≤ q := by exact_mod_cast h4
  have hz : ((q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1) * ((q : ℤ) ^ 4 - (q : ℤ) ^ 2) = 0 := by
    linear_combination key2
  have hpos : (0 : ℤ) < ((q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1) * ((q : ℤ) ^ 4 - (q : ℤ) ^ 2) := by
    have a1 : (0 : ℤ) < (q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1 := by positivity
    have a2 : (0 : ℤ) < (q : ℤ) ^ 4 - (q : ℤ) ^ 2 := by nlinarith [pow_pos (show (0 : ℤ) < q by omega) 2]
    exact mul_pos a1 a2
  linarith

theorem g2_ne_TD4 {e M : ℕ} (he : 2 ≤ e)
    (hM : M * lieOrderDivisor .G2 0 (2 ^ (2 * e)) = lieOrderNumerator .G2 0 (2 ^ (2 * e)))
    (hM' : M * lieOrderDivisor .trialityD4 0 (2 ^ e) = lieOrderNumerator .trialityD4 0 (2 ^ e)) :
    False := by
  have h4 : 4 ≤ 2 ^ e := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hD : lieOrderDivisor .G2 0 (2 ^ (2 * e)) = 1 := rfl
  rw [hD, mul_one] at hM
  have hM2 := order_TD4 hM'
  rw [pow_mul'] at hM
  generalize 2 ^ e = q at h4 hM hM2
  have e1 : M = q ^ 12 * ((q ^ 12 - 1) * (q ^ 4 - 1)) := by
    rw [hM]
    show ((q ^ 2) ^ 6 * ((q ^ 2) ^ 6 - 1) * ((q ^ 2) ^ 2 - 1)) = _
    have a1 : (q ^ 2) ^ 6 = q ^ 12 := by ring
    have a2 : (q ^ 2) ^ 2 = q ^ 4 := by ring
    rw [a1, a2]
    ring
  have key : q ^ 12 * ((q ^ 12 - 1) * (q ^ 4 - 1)) =
      q ^ 12 * (((q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1)) * (q ^ 2 - 1)) := by
    rw [← e1, hM2]
    ring
  have hq12 : 0 < q ^ 12 := by positivity
  have key1 := Nat.eq_of_mul_eq_mul_left hq12 key
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h4' : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h12 : 1 ≤ q ^ 12 := Nat.one_le_pow _ _ (by omega)
  zify [h2, h4', h6, h12] at key1
  have hQ : (4 : ℤ) ≤ q := by exact_mod_cast h4
  have hz : ((q : ℤ) ^ 6 - 1) * (((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 6 - (q : ℤ) ^ 4 + (q : ℤ) ^ 2)) = 0 := by
    linear_combination key1
  have a1 : (1 : ℤ) < (q : ℤ) ^ 2 := by nlinarith
  have a2 : (1 : ℤ) < (q : ℤ) ^ 6 := by nlinarith [pow_pos (show (0 : ℤ) < q by omega) 4]
  have a3 : (0 : ℤ) < (q : ℤ) ^ 6 - (q : ℤ) ^ 4 + (q : ℤ) ^ 2 := by
    have : (q : ℤ) ^ 4 < (q : ℤ) ^ 6 := by nlinarith [pow_pos (show (0 : ℤ) < q by omega) 4]
    nlinarith
  have hpos := mul_pos (sub_pos.mpr a2) (mul_pos (sub_pos.mpr a1) a3)
  linarith


theorem mul_pow_le {x : ℤ} (hx : 2 ≤ x) (a b : ℕ) (c : ℤ) (hc : c ≤ 2 ^ b) :
    c * x ^ a ≤ x ^ (a + b) := by
  have hx0 : (0 : ℤ) ≤ x := by linarith
  calc c * x ^ a ≤ 2 ^ b * x ^ a := mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ x ^ b * x ^ a :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hx b) (by positivity)
    _ = x ^ (a + b) := by ring

theorem sp3_ne_TD4 {j M : ℕ} (hj : 1 ≤ j)
    (hM : M * lieOrderDivisor .PSp 3 (2 ^ (4 * j)) = lieOrderNumerator .PSp 3 (2 ^ (4 * j)))
    (hM' : M * lieOrderDivisor .trialityD4 0 (2 ^ (3 * j)) =
      lieOrderNumerator .trialityD4 0 (2 ^ (3 * j))) : False := by
  have hx : 2 ≤ 2 ^ j := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  have hM1 := order_Sp (by omega) hM
  have hM2 := order_TD4 hM'
  rw [pow_mul'] at hM1 hM2
  generalize 2 ^ j = x at hx hM1 hM2
  have e1 : M = x ^ 36 * ((x ^ 8 - 1) * (x ^ 16 - 1) * (x ^ 24 - 1)) := by
    rw [hM1]
    have hp : (∏ i ∈ Finset.Icc 1 3, ((x ^ 4) ^ (2 * i) - 1)) =
        ((x ^ 4) ^ 2 - 1) * ((x ^ 4) ^ 4 - 1) * ((x ^ 4) ^ 6 - 1) := by
      simp [Finset.prod_Icc_succ_top]
    rw [hp]
    have a1 : (x ^ 4) ^ 2 = x ^ 8 := by ring
    have a2 : (x ^ 4) ^ 4 = x ^ 16 := by ring
    have a3 : (x ^ 4) ^ 6 = x ^ 24 := by ring
    have a4 : (x ^ 4) ^ (3 ^ 2) = x ^ 36 := by ring
    rw [a1, a2, a3, a4]
  have e2 : M = x ^ 36 * ((x ^ 24 + x ^ 12 + 1) * (x ^ 18 - 1) * (x ^ 6 - 1)) := by
    rw [hM2]
    have b1 : (x ^ 3) ^ 12 = x ^ 36 := by ring
    have b2 : (x ^ 3) ^ 8 = x ^ 24 := by ring
    have b3 : (x ^ 3) ^ 4 = x ^ 12 := by ring
    have b4 : (x ^ 3) ^ 6 = x ^ 18 := by ring
    have b5 : (x ^ 3) ^ 2 = x ^ 6 := by ring
    rw [b1, b2, b3, b4, b5]
    ring
  have hx36 : 0 < x ^ 36 := by positivity
  have key := Nat.eq_of_mul_eq_mul_left hx36 (e1.symm.trans e2)
  have h6 : 1 ≤ x ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h8 : 1 ≤ x ^ 8 := Nat.one_le_pow _ _ (by omega)
  have h16 : 1 ≤ x ^ 16 := Nat.one_le_pow _ _ (by omega)
  have h18 : 1 ≤ x ^ 18 := Nat.one_le_pow _ _ (by omega)
  have h24 : 1 ≤ x ^ 24 := Nat.one_le_pow _ _ (by omega)
  zify [h6, h8, h16, h18, h24] at key
  have hxz : (2 : ℤ) ≤ x := by exact_mod_cast hx
  have hz : (x : ℤ) ^ 42 - (x : ℤ) ^ 40 - (x : ℤ) ^ 36 - (x : ℤ) ^ 32 + 2 * (x : ℤ) ^ 30 -
      2 * (x : ℤ) ^ 24 + 2 * (x : ℤ) ^ 18 + (x : ℤ) ^ 16 - (x : ℤ) ^ 12 + (x : ℤ) ^ 8 +
      (x : ℤ) ^ 6 - 2 = 0 := by
    linear_combination key
  have p1 : 4 * (x : ℤ) ^ 40 ≤ (x : ℤ) ^ 42 := mul_pow_le hxz 40 2 4 (by norm_num)
  have p36 : 16 * (x : ℤ) ^ 36 ≤ (x : ℤ) ^ 40 := mul_pow_le hxz 36 4 16 (by norm_num)
  have p32 : 16 * (x : ℤ) ^ 32 ≤ (x : ℤ) ^ 40 := mul_pow_le hxz 32 8 16 (by norm_num)
  have p24 : 32 * (x : ℤ) ^ 24 ≤ (x : ℤ) ^ 40 := mul_pow_le hxz 24 16 32 (by norm_num)
  have p12 : 16 * (x : ℤ) ^ 12 ≤ (x : ℤ) ^ 40 := mul_pow_le hxz 12 28 16 (by norm_num)
  have p0 : 32 * (x : ℤ) ^ 0 ≤ (x : ℤ) ^ 40 := mul_pow_le hxz 0 40 32 (by norm_num)
  have hx0 : (0 : ℤ) ≤ x := by linarith
  have q30 : (0 : ℤ) ≤ (x : ℤ) ^ 30 := by positivity
  have q18 : (0 : ℤ) ≤ (x : ℤ) ^ 18 := by positivity
  have q16 : (0 : ℤ) ≤ (x : ℤ) ^ 16 := by positivity
  have q8 : (0 : ℤ) ≤ (x : ℤ) ^ 8 := by positivity
  have q6 : (0 : ℤ) ≤ (x : ℤ) ^ 6 := by positivity
  simp only [pow_zero, mul_one] at p0
  linarith

theorem td4_excl_sp {n f e M : ℕ} (he : 2 ≤ e) (hadm : StatedLieAdmissible .PSp n 2 f)
    (hM : M * lieOrderDivisor .PSp n (2 ^ f) = lieOrderNumerator .PSp n (2 ^ f))
    (hM' : M * lieOrderDivisor .trialityD4 0 (2 ^ e) = lieOrderNumerator .trialityD4 0 (2 ^ e)) :
    False := by
  have hadm' : StatedLieAdmissible .trialityD4 0 2 e := ⟨Nat.prime_two, by omega, rfl⟩
  have hv := v2_eq_of_two hadm hM hadm' hM'
  rw [sylowExp_TD4] at hv
  have hn : 2 ≤ n := hadm.2.2.1
  have hsyl : lieSylowExponent .PSp n = n ^ 2 := rfl
  rw [hsyl] at hv
  by_cases h4 : 4 ≤ n
  · refine td4_excl_crude he hadm hM hM' ?_
    simp only [cofE, lieSylowExponent]
    nlinarith
  · have hn3 : n = 2 ∨ n = 3 := by omega
    rcases hn3 with rfl | rfl
    · have hfe : f = 3 * e := by omega
      subst hfe
      exact sp2_ne_TD4 he hM hM'
    · obtain ⟨j, rfl, rfl⟩ : ∃ j, e = 3 * j ∧ f = 4 * j := ⟨e / 3, by omega, by omega⟩
      exact sp3_ne_TD4 (by omega) hM hM'

theorem td4_excl_g2 {n f e M : ℕ} (he : 2 ≤ e) (hadm : StatedLieAdmissible .G2 n 2 f)
    (hM : M * lieOrderDivisor .G2 n (2 ^ f) = lieOrderNumerator .G2 n (2 ^ f))
    (hM' : M * lieOrderDivisor .trialityD4 0 (2 ^ e) = lieOrderNumerator .trialityD4 0 (2 ^ e)) :
    False := by
  have hadm' : StatedLieAdmissible .trialityD4 0 2 e := ⟨Nat.prime_two, by omega, rfl⟩
  have hv := v2_eq_of_two hadm hM hadm' hM'
  rw [sylowExp_TD4] at hv
  have hn : n = 0 := hadm.2.2.1
  subst hn
  have hsyl : lieSylowExponent .G2 0 = 6 := rfl
  rw [hsyl] at hv
  have hfe : f = 2 * e := by omega
  subst hfe
  exact g2_ne_TD4 he hM hM'

theorem td4_excl_ree {n f e M : ℕ} (he : 2 ≤ e) (hadm : StatedLieAdmissible .twistedF4 n 2 f)
    (hM : M * lieOrderDivisor .twistedF4 n (2 ^ f) = lieOrderNumerator .twistedF4 n (2 ^ f))
    (hM' : M * lieOrderDivisor .trialityD4 0 (2 ^ e) = lieOrderNumerator .trialityD4 0 (2 ^ e)) :
    False :=
  td4_excl_crude he hadm hM hM' (by simp [cofE, lieSylowExponent])

end TD4B

end CFSG.LocalAnalysis.GLTheoremA.HDesc
