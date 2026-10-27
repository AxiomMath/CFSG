module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Arith

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof (lieOrderCofactor lieOrderNumerator_eq)
open CFSG.SeitzReduction.CrossChar
open Finset

section Comparators

open scoped Nat

theorem v2_eq_of_two {t t' : StatedLieTag} {n n' f f' M : ℕ}
    (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hadm' : StatedLieAdmissible t' n' 2 f')
    (hM' : M * lieOrderDivisor t' n' (2 ^ f') = lieOrderNumerator t' n' (2 ^ f')) :
    lieSylowExponent t n * f = lieSylowExponent t' n' * f' := by
  have h1 := ordProj_two_eq_of_two hadm hM
  have h2 := ordProj_two_eq_of_two hadm' hM'
  rw [h1] at h2
  exact Nat.pow_right_injective le_rfl h2

theorem order_L2 {e M : ℕ} (he : 1 ≤ e)
    (hM : M * lieOrderDivisor .PSL 2 (2 ^ e) = lieOrderNumerator .PSL 2 (2 ^ e)) :
    M = 2 ^ e * ((2 ^ e) ^ 2 - 1) := by
  have hD : lieOrderDivisor .PSL 2 (2 ^ e) = 1 := by
    show Nat.gcd 2 (2 ^ e - 1) = 1
    have h2 : 2 ≤ 2 ^ e := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    have : Odd (2 ^ e - 1) := by
      have : Even (2 ^ e) := Nat.even_pow.mpr ⟨even_two, by omega⟩
      exact Nat.Even.sub_odd (by omega) this odd_one
    exact Nat.coprime_two_left.mpr this
  rw [hD, mul_one] at hM
  rw [hM]
  simp [lieOrderNumerator]

theorem cube_le_four_mul_L2 {e M : ℕ} (he : 1 ≤ e)
    (hM : M * lieOrderDivisor .PSL 2 (2 ^ e) = lieOrderNumerator .PSL 2 (2 ^ e)) :
    (2 ^ e) ^ 3 ≤ 4 * M := by
  rw [order_L2 he hM]
  have h2 : 2 ≤ 2 ^ e := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  generalize 2 ^ e = Q at h2 ⊢
  have h1 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h1]
  nlinarith

theorem adm_L2 {e : ℕ} (he : 2 ≤ e) : StatedLieAdmissible .PSL 2 2 e := by
  have h4 : 4 ≤ 2 ^ e := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  refine ⟨Nat.prime_two, by omega, le_rfl, fun h => ?_, fun h => ?_⟩
  · have := (Prod.mk.inj h).2
    omega
  · have := (Prod.mk.inj h).2
    omega

theorem sylowExp_L2 : lieSylowExponent .PSL 2 = 1 := by
  simp [lieSylowExponent]

theorem cls_L2 {t : StatedLieTag} {e n f M : ℕ} (he : 2 ≤ e) (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hM' : M * lieOrderDivisor .PSL 2 (2 ^ e) = lieOrderNumerator .PSL 2 (2 ^ e)) :
    (t = .PSL ∧ n = 2 ∧ f = e) ∨ (t = .PSL ∧ n = 3 ∧ f = 1) := by
  have hadm' := adm_L2 he
  have hv := v2_eq_of_two hadm hM hadm' hM'
  rw [sylowExp_L2, one_mul] at hv
  by_cases h2 : t = .PSL ∧ n = 2
  · obtain ⟨rfl, rfl⟩ := h2
    left
    refine ⟨rfl, rfl, ?_⟩
    rw [sylowExp_L2, one_mul] at hv
    exact hv
  · by_cases h3 : t = .PSL ∧ n = 3 ∧ f = 1
    · exact Or.inr h3
    · exfalso
      have hlt := (lt_cube_of_two hadm hM).2 h2 h3
      have hcube := cube_le_four_mul_L2 (by omega : 1 ≤ e) hM'
      have h1 := ordProj_two_eq_of_two hadm hM
      rw [h1, hv] at hlt
      rw [← pow_mul] at hcube hlt
      omega

theorem adm_L3 {e : ℕ} (he : 1 ≤ e) : StatedLieAdmissible .PSL 3 2 e :=
  ⟨Nat.prime_two, he, by norm_num, fun h => by have := (Prod.mk.inj h).1; omega,
    fun h => by have := (Prod.mk.inj h).1; omega⟩

theorem adm_U3 {e : ℕ} (he : 2 ≤ e) : StatedLieAdmissible .PSU 3 2 e := by
  have h4 : 4 ≤ 2 ^ e := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  refine ⟨Nat.prime_two, by omega, le_rfl, fun h => ?_⟩
  have := (Prod.mk.inj h).2
  omega

theorem sylowExp_L3 : lieSylowExponent .PSL 3 = 3 := by simp [lieSylowExponent]

theorem sylowExp_U3 : lieSylowExponent .PSU 3 = 3 := by simp [lieSylowExponent]

theorem num_L3 (Q : ℕ) :
    lieOrderNumerator .PSL 3 Q = Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) := by
  have : (∏ i ∈ Finset.Icc 2 3, (Q ^ i - 1)) = (Q ^ 2 - 1) * (Q ^ 3 - 1) := by
    simp [Finset.prod_Icc_succ_top]
  simp only [lieOrderNumerator, this]

theorem num_U3 (Q : ℕ) :
    lieOrderNumerator .PSU 3 Q = Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) := by
  have : (∏ i ∈ Finset.Icc 2 3, (if Even i then Q ^ i - 1 else Q ^ i + 1)) =
      (Q ^ 2 - 1) * (Q ^ 3 + 1) := by
    simp [Finset.prod_Icc_succ_top, Nat.even_iff]
  simp only [lieOrderNumerator, this]

theorem three_dvd_pow_two_sub_one {e : ℕ} (he : Even e) : 3 ∣ 2 ^ e - 1 := by
  obtain ⟨m, rfl⟩ := he
  have : 2 ^ (m + m) = 4 ^ m := by rw [← two_mul, pow_mul]; norm_num
  rw [this]
  simpa using Nat.sub_dvd_pow_sub_pow 4 1 m

theorem three_dvd_pow_two_add_one {e : ℕ} (he : Odd e) : 3 ∣ 2 ^ e + 1 := by
  simpa using Odd.nat_add_dvd_pow_add_pow 2 1 he

theorem big_of_P {Q M P : ℕ} (hQ : 16 ≤ Q) (hP : 9 * Q ^ 5 ≤ 10 * P) (hM : M * 3 = Q ^ 3 * P) :
    (Q ^ 3) ^ 5 < M ^ 2 := by
  by_contra hcon
  push Not at hcon
  have h1 : 9 * Q ^ 8 ≤ 30 * M := by
    calc 9 * Q ^ 8 = Q ^ 3 * (9 * Q ^ 5) := by ring
      _ ≤ Q ^ 3 * (10 * P) := Nat.mul_le_mul_left _ hP
      _ = 10 * (Q ^ 3 * P) := by ring
      _ = 10 * (M * 3) := by rw [hM]
      _ = 30 * M := by ring
  have h2 : (9 * Q ^ 8) ^ 2 ≤ (30 * M) ^ 2 := Nat.pow_le_pow_left h1 2
  have h3 : 9 * Q ^ 16 ≤ 100 * M ^ 2 := by nlinarith
  have h4 : 100 * M ^ 2 ≤ 100 * (Q ^ 3) ^ 5 := Nat.mul_le_mul_left _ hcon
  have h5 : 9 * Q ^ 16 ≤ 100 * Q ^ 15 := by
    calc 9 * Q ^ 16 ≤ 100 * M ^ 2 := h3
      _ ≤ 100 * (Q ^ 3) ^ 5 := h4
      _ = 100 * Q ^ 15 := by ring
  have h6 : 9 * Q * Q ^ 15 ≤ 100 * Q ^ 15 := by
    calc 9 * Q * Q ^ 15 = 9 * Q ^ 16 := by ring
      _ ≤ 100 * Q ^ 15 := h5
  have h7 : 9 * Q ≤ 100 := Nat.le_of_mul_le_mul_right h6 (by positivity)
  omega

theorem bigP_L3 {Q : ℕ} (hQ : 16 ≤ Q) : 9 * Q ^ 5 ≤ 10 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) := by
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ (by omega)
  zify [h2, h3]
  have hQ' : (16 : ℤ) ≤ Q := by exact_mod_cast hQ
  nlinarith [pow_pos (show (0 : ℤ) < Q by omega) 2, pow_pos (show (0 : ℤ) < Q by omega) 3,
    pow_pos (show (0 : ℤ) < Q by omega) 4]

theorem bigP_U3 {Q : ℕ} (hQ : 16 ≤ Q) : 9 * Q ^ 5 ≤ 10 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) := by
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h2]
  have hQ' : (16 : ℤ) ≤ Q := by exact_mod_cast hQ
  nlinarith [pow_pos (show (0 : ℤ) < Q by omega) 2, pow_pos (show (0 : ℤ) < Q by omega) 3,
    pow_pos (show (0 : ℤ) < Q by omega) 4]

theorem cancel_L3U3 {Q M D1 D2 : ℕ} (hQ : 2 ≤ Q) {a b : ℕ}
    (h1 : M * D1 = Q ^ 3 * ((Q ^ 2 - 1) * a)) (h2 : M * D2 = Q ^ 3 * ((Q ^ 2 - 1) * b)) :
    D2 * a = D1 * b := by
  have hpos : 0 < Q ^ 3 * (Q ^ 2 - 1) := by
    have : 1 < Q ^ 2 := by nlinarith
    exact Nat.mul_pos (pow_pos (by omega) 3) (Nat.sub_pos_of_lt this)
  have h3 : D2 * (M * D1) = D1 * (M * D2) := by ring
  rw [h1, h2] at h3
  have h4 : (Q ^ 3 * (Q ^ 2 - 1)) * (D2 * a) = (Q ^ 3 * (Q ^ 2 - 1)) * (D1 * b) := by
    calc (Q ^ 3 * (Q ^ 2 - 1)) * (D2 * a) = D2 * (Q ^ 3 * ((Q ^ 2 - 1) * a)) := by ring
      _ = D1 * (Q ^ 3 * ((Q ^ 2 - 1) * b)) := h3
      _ = (Q ^ 3 * (Q ^ 2 - 1)) * (D1 * b) := by ring
  exact Nat.eq_of_mul_eq_mul_left hpos h4

theorem cls_L3 {t : StatedLieTag} {m n f M : ℕ} (hm : 2 ≤ m) (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hM' : M * lieOrderDivisor .PSL 3 (2 ^ (2 * m)) = lieOrderNumerator .PSL 3 (2 ^ (2 * m))) :
    t = .PSL ∧ n = 3 ∧ f = 2 * m := by
  have hadm' := adm_L3 (e := 2 * m) (by omega)
  have hv := v2_eq_of_two hadm hM hadm' hM'
  rw [sylowExp_L3] at hv
  have hQ16 : 16 ≤ 2 ^ (2 * m) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hM'o := hM'
  have hD3 : lieOrderDivisor .PSL 3 (2 ^ (2 * m)) = 3 := by
    show Nat.gcd 3 (2 ^ (2 * m) - 1) = 3
    exact Nat.gcd_eq_left (three_dvd_pow_two_sub_one (even_two_mul m))
  rw [hD3, num_L3] at hM'
  have hbig := big_of_P hQ16 (bigP_L3 hQ16) hM'
  have e3 : (2 ^ (2 * m)) ^ 3 = 2 ^ (3 * (2 * m)) := by rw [← pow_mul, mul_comm]
  by_cases hshape : (t = .PSL ∧ (n = 2 ∨ n = 3)) ∨ (t = .PSU ∧ n = 3)
  · rcases hshape with ⟨rfl, hn⟩ | ⟨rfl, rfl⟩
    · rcases hn with rfl | rfl
      · exfalso
        have hlt := (lt_cube_of_two hadm' hM'o).2 (fun h => by have := h.2; omega)
          (fun h => by have := h.2.2; omega)
        have hge := cube_le_four_mul_L2 (by have := hadm.2.1; omega) hM
        have h1 := ordProj_two_eq_of_two hadm' hM'o
        rw [h1, sylowExp_L3] at hlt
        rw [sylowExp_L2, one_mul] at hv
        rw [hv] at hge
        rw [← pow_mul] at hge hlt
        omega
      · refine ⟨rfl, rfl, ?_⟩
        rw [sylowExp_L3] at hv
        omega
    · exfalso
      have hf : f = 2 * m := by rw [sylowExp_U3] at hv; omega
      subst hf
      have hDU : lieOrderDivisor .PSU 3 (2 ^ (2 * m)) ∣ 3 := Nat.gcd_dvd_left _ _
      rw [num_U3] at hM
      have hc := cancel_L3U3 (Q := 2 ^ (2 * m)) (by omega) hM hM'
      rcases (Nat.dvd_prime Nat.prime_three).mp hDU with h | h
      · rw [h] at hc
        have : 1 ≤ (2 ^ (2 * m)) ^ 3 := Nat.one_le_pow _ _ (by omega)
        omega
      · rw [h] at hc
        have : 1 ≤ (2 ^ (2 * m)) ^ 3 := Nat.one_le_pow _ _ (by omega)
        omega
  · exfalso
    have hlt := univ_lt hadm hshape hM
    rw [hv] at hlt
    rw [e3] at hbig
    omega

theorem cls_U3 {t : StatedLieTag} {k n f M : ℕ} (hk : Odd k) (h5 : 5 ≤ k)
    (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hM' : M * lieOrderDivisor .PSU 3 (2 ^ k) = lieOrderNumerator .PSU 3 (2 ^ k)) :
    t = .PSU ∧ n = 3 ∧ f = k := by
  have hadm' := adm_U3 (e := k) (by omega)
  have hv := v2_eq_of_two hadm hM hadm' hM'
  rw [sylowExp_U3] at hv
  have hQ16 : 16 ≤ 2 ^ k := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hM'o := hM'
  have hD3 : lieOrderDivisor .PSU 3 (2 ^ k) = 3 := by
    show Nat.gcd 3 (2 ^ k + 1) = 3
    exact Nat.gcd_eq_left (three_dvd_pow_two_add_one hk)
  rw [hD3, num_U3] at hM'
  have hbig := big_of_P hQ16 (bigP_U3 hQ16) hM'
  have e3 : (2 ^ k) ^ 3 = 2 ^ (3 * k) := by rw [← pow_mul, mul_comm]
  by_cases hshape : (t = .PSL ∧ (n = 2 ∨ n = 3)) ∨ (t = .PSU ∧ n = 3)
  · rcases hshape with ⟨rfl, hn⟩ | ⟨rfl, rfl⟩
    · rcases hn with rfl | rfl
      · exfalso
        have hlt := (lt_cube_of_two hadm' hM'o).2 (fun h => by cases h.1)
          (fun h => by cases h.1)
        have hge := cube_le_four_mul_L2 (by have := hadm.2.1; omega) hM
        have h1 := ordProj_two_eq_of_two hadm' hM'o
        rw [h1, sylowExp_U3] at hlt
        rw [sylowExp_L2, one_mul] at hv
        rw [hv] at hge
        rw [← pow_mul] at hge hlt
        omega
      · exfalso
        have hf : f = k := by rw [sylowExp_L3] at hv; omega
        subst hf
        have hDL : lieOrderDivisor .PSL 3 (2 ^ f) ∣ 3 := Nat.gcd_dvd_left _ _
        rw [num_L3] at hM
        have hc := cancel_L3U3 (Q := 2 ^ f) (by omega) hM hM'
        have hx : 100 ≤ (2 ^ f) ^ 3 := by
          calc 100 ≤ 16 ^ 3 := by norm_num
            _ ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left hQ16 3
        rcases (Nat.dvd_prime Nat.prime_three).mp hDL with h | h
        · rw [h] at hc
          omega
        · rw [h] at hc
          omega
    · exact ⟨rfl, rfl, by rw [sylowExp_U3] at hv; omega⟩
  · exfalso
    have hlt := univ_lt hadm hshape hM
    rw [hv] at hlt
    rw [e3] at hbig
    omega

end Comparators

end CFSG.LocalAnalysis.GLTheoremA.HDesc
