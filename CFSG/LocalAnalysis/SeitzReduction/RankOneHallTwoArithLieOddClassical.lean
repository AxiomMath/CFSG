module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithLieOddFactor
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

namespace CFSG.SeitzReduction.RankOne.LieOdd

open Finset

theorem tri_succ (m : ℕ) : (m + 1) * (m + 1 - 1) / 2 = m * (m - 1) / 2 + m := by
  rw [Nat.add_sub_cancel]
  cases m with
  | zero => rfl
  | succ k =>
    rw [show (k + 1 + 1) * (k + 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1) by
      rw [Nat.add_sub_cancel]; ring, Nat.add_mul_div_left _ _ (by norm_num)]

theorem twoPartBound_prod_Icc_two {q : ℕ} (x : ℕ → ℕ)
    (hx : ∀ i, 1 ≤ i → TwoPartBound (x i) (q ^ (i - 1) * (q - 1)) ((q + 1) * ordProj[2] i))
    {m : ℕ} (hm : 1 ≤ m) :
    TwoPartBound (∏ i ∈ Icc 2 m, x i) (q ^ (m * (m - 1) / 2) * (q - 1) ^ (m - 1))
      ((q + 1) ^ (m - 1) * ordProj[2] m.factorial) := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [Finset.Icc_eq_empty (by norm_num)]
    simpa using twoPartBound_one
  | succ m hm ih =>
    rw [Finset.prod_Icc_succ_top (by omega)]
    refine (ih.mul (hx (m + 1) (by omega))).mono (le_of_eq ?_) (le_of_eq ?_)
    · rw [tri_succ, Nat.add_sub_cancel, pow_add]
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    · rw [Nat.factorial_succ, Nat.ordProj_mul 2 (by omega) (Nat.factorial_ne_zero m),
        Nat.add_sub_cancel]
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring

theorem twoPartBound_prod_Icc_one {q : ℕ} (hq : 3 ≤ q) (hqodd : Odd q) (m : ℕ) :
    TwoPartBound (∏ i ∈ Icc 1 m, (q ^ (2 * i) - 1)) (q ^ (m ^ 2) * (q - 1) ^ m)
      ((q + 1) ^ m * 2 ^ m * ordProj[2] m.factorial) := by
  induction m with
  | zero =>
    rw [Finset.Icc_eq_empty (by norm_num)]
    simpa using twoPartBound_one
  | succ m ih =>
    rw [Finset.prod_Icc_succ_top (by omega)]
    have hf := twoPartBound_pow_sub_one' hq hqodd (a := 2 * (m + 1)) (by omega)
    refine (ih.mul hf).mono (le_of_eq ?_) (le_of_eq ?_)
    · rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
      ring
    · rw [Nat.factorial_succ, Nat.ordProj_mul 2 (by omega) (Nat.factorial_ne_zero m),
        Nat.ordProj_mul 2 (by norm_num) (by omega), Nat.Prime.factorization_self Nat.prime_two]
      ring

theorem twoPartBound_omega {q m X : ℕ} (hq : 3 ≤ q) (hqodd : Odd q) (hm : 1 ≤ m)
    (hX : TwoPartBound X (q ^ (m - 1) * (q - 1)) ((q + 1) * ordProj[2] m)) :
    TwoPartBound (X * ∏ i ∈ Icc 1 (m - 1), (q ^ (2 * i) - 1)) (q ^ (m * (m - 1)) * (q - 1) ^ m)
      ((q + 1) ^ m * 2 ^ (m - 1) * ordProj[2] m.factorial) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hX ⊢
  refine (hX.mul (twoPartBound_prod_Icc_one hq hqodd k)).mono (le_of_eq ?_) (le_of_eq ?_)
  · ring
  · rw [Nat.factorial_succ, Nat.ordProj_mul 2 (by omega) (Nat.factorial_ne_zero k)]
    ring

theorem ordProj_two_factorial_le {m : ℕ} (hm : 1 ≤ m) :
    ordProj[2] m.factorial ≤ 2 ^ (m - 1) := by
  apply Nat.pow_le_pow_right (by norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.factorization_def _ Nat.prime_two]
  have := padicValNat_factorial_lt_of_ne_zero 2 (show m ≠ 0 by omega)
  omega

theorem twoPartBound_psu_factor {q i : ℕ} (hq : 3 ≤ q) (hqodd : Odd q) (hi : 1 ≤ i) :
    TwoPartBound (if Even i then q ^ i - 1 else q ^ i + 1) (q ^ (i - 1) * (q - 1))
      ((q + 1) * ordProj[2] i) := by
  split_ifs
  · exact twoPartBound_pow_sub_one' hq hqodd hi
  · exact (twoPartBound_pow_add_one hq hqodd hi).mono le_rfl
      (Nat.le_mul_of_pos_right _ (by positivity))

theorem aux_typeA (k : ℕ) :
    2 ^ (5 * k + 20) * ((2 * k + 8) * (k + 5)) ≤ 3 ^ (k ^ 2 + 9 * k + 19) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have e3 : (2 * (k + 1) + 8) * (k + 1 + 5) ≤ 2 * ((2 * k + 8) * (k + 5)) := by nlinarith
    have e4 : 64 ≤ 3 ^ (2 * k + 10) :=
      calc 64 ≤ 3 ^ 10 := by norm_num
        _ ≤ 3 ^ (2 * k + 10) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 ^ (5 * (k + 1) + 20) * ((2 * (k + 1) + 8) * (k + 1 + 5))
        = 2 ^ (5 * k + 20) * 32 * ((2 * (k + 1) + 8) * (k + 1 + 5)) := by ring
      _ ≤ 2 ^ (5 * k + 20) * 32 * (2 * ((2 * k + 8) * (k + 5))) := by gcongr
      _ = 64 * (2 ^ (5 * k + 20) * ((2 * k + 8) * (k + 5))) := by ring
      _ ≤ 64 * 3 ^ (k ^ 2 + 9 * k + 19) := by gcongr
      _ ≤ 3 ^ (2 * k + 10) * 3 ^ (k ^ 2 + 9 * k + 19) := by gcongr
      _ = 3 ^ ((k + 1) ^ 2 + 9 * (k + 1) + 19) := by ring

theorem aux_typeB (k : ℕ) :
    2 ^ (7 * k + 19) * ((3 * k + 8) * 2) ≤ 3 ^ (2 * k ^ 2 + 12 * k + 17) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have e3 : (3 * (k + 1) + 8) * 2 ≤ 2 * ((3 * k + 8) * 2) := by omega
    have e4 : 256 ≤ 3 ^ (4 * k + 14) :=
      calc 256 ≤ 3 ^ 14 := by norm_num
        _ ≤ 3 ^ (4 * k + 14) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 ^ (7 * (k + 1) + 19) * ((3 * (k + 1) + 8) * 2)
        = 2 ^ (7 * k + 19) * 128 * ((3 * (k + 1) + 8) * 2) := by ring
      _ ≤ 2 ^ (7 * k + 19) * 128 * (2 * ((3 * k + 8) * 2)) := by gcongr
      _ = 256 * (2 ^ (7 * k + 19) * ((3 * k + 8) * 2)) := by ring
      _ ≤ 256 * 3 ^ (2 * k ^ 2 + 12 * k + 17) := by gcongr
      _ ≤ 3 ^ (4 * k + 14) * 3 ^ (2 * k ^ 2 + 12 * k + 17) := by gcongr
      _ = 3 ^ (2 * (k + 1) ^ 2 + 12 * (k + 1) + 17) := by ring

theorem aux_typeC (k : ℕ) :
    2 ^ (7 * k + 24) * ((3 * k + 10) * 4) ≤ 3 ^ (2 * k ^ 2 + 14 * k + 23) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have e3 : (3 * (k + 1) + 10) * 4 ≤ 2 * ((3 * k + 10) * 4) := by omega
    have e4 : 256 ≤ 3 ^ (4 * k + 16) :=
      calc 256 ≤ 3 ^ 16 := by norm_num
        _ ≤ 3 ^ (4 * k + 16) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 ^ (7 * (k + 1) + 24) * ((3 * (k + 1) + 10) * 4)
        = 2 ^ (7 * k + 24) * 128 * ((3 * (k + 1) + 10) * 4) := by ring
      _ ≤ 2 ^ (7 * k + 24) * 128 * (2 * ((3 * k + 10) * 4)) := by gcongr
      _ = 256 * (2 ^ (7 * k + 24) * ((3 * k + 10) * 4)) := by ring
      _ ≤ 256 * 3 ^ (2 * k ^ 2 + 14 * k + 23) := by gcongr
      _ ≤ 3 ^ (4 * k + 16) * 3 ^ (2 * k ^ 2 + 14 * k + 23) := by gcongr
      _ = 3 ^ (2 * (k + 1) ^ 2 + 14 * (k + 1) + 23) := by ring

theorem lieOdd_typeA {q m e h g : ℕ} (x : ℕ → ℕ)
    (hx : ∀ i, 1 ≤ i → TwoPartBound (x i) (q ^ (i - 1) * (q - 1)) ((q + 1) * ordProj[2] i))
    (hq : 3 ≤ q) (hqodd : Odd q) (hm : 3 ≤ m)
    (heq : q ^ (m * (m - 1) / 2) * ∏ i ∈ Icc 2 m, x i = 2 ^ e * h * g) (hg : g ≤ m)
    (he1 : 1 ≤ e) (hdiv : h ∣ (2 ^ e - 1) * e) :
    (m = 3 ∧ q < 7) ∨ (m = 4 ∧ q < 5) := by
  have hb := twoPartBound_prod_Icc_two x hx (by omega : 1 ≤ m)
  rcases (by omega : m = 3 ∨ m = 4 ∨ 5 ≤ m) with rfl | rfl | h5
  · left
    refine ⟨rfl, ?_⟩
    have hf : ordProj[2] (Nat.factorial 3) = 2 ^ 1 := by
      rw [show Nat.factorial 3 = 2 ^ 1 * 3 by decide]
      exact ordProj_two_pow_mul_odd (by decide)
    rw [hf] at hb
    have hc := lt_of_twoPartBound hq hqodd heq hb hg he1 hdiv (M := 3) (by norm_num)
    by_contra hq7
    have h7 : 7 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left (by omega) 3
    norm_num at hc h7
    omega
  · right
    refine ⟨rfl, ?_⟩
    have hf : ordProj[2] (Nat.factorial 4) = 2 ^ 3 := by
      rw [show Nat.factorial 4 = 2 ^ 3 * 3 by decide]
      exact ordProj_two_pow_mul_odd (by decide)
    rw [hf] at hb
    have hc := lt_of_twoPartBound hq hqodd heq hb hg he1 hdiv (M := 8) (by norm_num)
    by_contra hq5
    have h7 : 5 ^ 8 ≤ q ^ 8 := Nat.pow_le_pow_left (by omega) 8
    norm_num at hc h7
    omega
  · exfalso
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 5 := ⟨m - 5, by omega⟩
    simp only [show k + 5 - 1 = k + 4 by omega] at hb heq
    have hb' := hb.mono le_rfl (Nat.mul_le_mul_left ((q + 1) ^ (k + 4))
      (ordProj_two_factorial_le (m := k + 4 + 1) (by omega)))
    simp only [Nat.add_sub_cancel] at hb'
    have hev : (k + 5) * (k + 4) = 2 * ((k + 5) * (k + 4) / 2) := by
      refine (Nat.two_mul_div_two_of_even ?_).symm
      have := Nat.even_mul_succ_self (k + 4)
      rwa [mul_comm, show k + 4 + 1 = k + 5 by ring] at this
    have hsq : (k + 5) * (k + 4) = k ^ 2 + 9 * k + 20 := by ring
    have hc := lt_of_twoPartBound hq hqodd heq hb' hg he1 hdiv (M := k ^ 2 + 8 * k + 15)
      (by omega)
    have h8 : (8 : ℕ) ^ (k + 4) * 4 ^ (k + 4) = 2 ^ (5 * k + 20) := by
      rw [← mul_pow, show 5 * k + 20 = 5 * (k + 4) by ring, pow_mul]
      norm_num
    have := calc 3 ^ (k ^ 2 + 9 * k + 19)
        = 3 ^ (k + 4) * 3 ^ (k ^ 2 + 8 * k + 15) := by ring
      _ ≤ 3 ^ (k + 4) * q ^ (k ^ 2 + 8 * k + 15) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hq _)
      _ < 8 ^ (k + 4) * 4 ^ (k + 4) * (k + 4 + (k + 4)) * (k + 5) := hc
      _ = 2 ^ (5 * k + 20) * ((2 * k + 8) * (k + 5)) := by rw [h8]; ring
      _ ≤ 3 ^ (k ^ 2 + 9 * k + 19) := aux_typeA k
    exact lt_irrefl _ this

theorem lieOdd_typeB {q m e h g : ℕ} (hq : 3 ≤ q) (hqodd : Odd q) (hm : 2 ≤ m)
    (heq : q ^ (m ^ 2) * ∏ i ∈ Icc 1 m, (q ^ (2 * i) - 1) = 2 ^ e * h * g) (hg : g ≤ 2)
    (he1 : 1 ≤ e) (hdiv : h ∣ (2 ^ e - 1) * e) : m = 2 ∧ q < 7 := by
  have hb := twoPartBound_prod_Icc_one hq hqodd m
  rcases (by omega : m = 2 ∨ 3 ≤ m) with rfl | h3
  · refine ⟨rfl, ?_⟩
    have hf : ordProj[2] (Nat.factorial 2) = 2 ^ 1 := by
      rw [show Nat.factorial 2 = 2 ^ 1 * 1 by decide]
      exact ordProj_two_pow_mul_odd (by decide)
    rw [hf] at hb
    have hb' : TwoPartBound (∏ i ∈ Icc 1 2, (q ^ (2 * i) - 1)) (q ^ (2 ^ 2) * (q - 1) ^ 2)
        ((q + 1) ^ 2 * 2 ^ 3) := hb.mono le_rfl (le_of_eq (by ring))
    have hc := lt_of_twoPartBound hq hqodd heq hb' hg he1 hdiv (M := 5) (by norm_num)
    by_contra hq7
    have h7 : 7 ^ 5 ≤ q ^ 5 := Nat.pow_le_pow_left (by omega) 5
    norm_num at hc h7
    omega
  · exfalso
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
    have hb' : TwoPartBound (∏ i ∈ Icc 1 (k + 3), (q ^ (2 * i) - 1))
        (q ^ ((k + 3) ^ 2) * (q - 1) ^ (k + 3)) ((q + 1) ^ (k + 3) * 2 ^ (2 * k + 5)) := by
      refine hb.mono le_rfl ?_
      have := ordProj_two_factorial_le (m := k + 2 + 1) (by omega)
      simp only [Nat.add_sub_cancel] at this
      calc (q + 1) ^ (k + 3) * 2 ^ (k + 3) * ordProj[2] (k + 3).factorial
          ≤ (q + 1) ^ (k + 3) * 2 ^ (k + 3) * 2 ^ (k + 2) := Nat.mul_le_mul_left _ this
        _ = (q + 1) ^ (k + 3) * 2 ^ (2 * k + 5) := by ring
    have hc := lt_of_twoPartBound hq hqodd heq hb' hg he1 hdiv
      (M := 2 * k ^ 2 + 11 * k + 14) (by ring)
    have h8 : (8 : ℕ) ^ (k + 3) * 4 ^ (2 * k + 5) = 2 ^ (7 * k + 19) := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul,
        ← pow_mul, ← pow_add]
      ring_nf
    have := calc 3 ^ (2 * k ^ 2 + 12 * k + 17)
        = 3 ^ (k + 3) * 3 ^ (2 * k ^ 2 + 11 * k + 14) := by ring
      _ ≤ 3 ^ (k + 3) * q ^ (2 * k ^ 2 + 11 * k + 14) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hq _)
      _ < 8 ^ (k + 3) * 4 ^ (2 * k + 5) * (k + 3 + (2 * k + 5)) * 2 := hc
      _ = 2 ^ (7 * k + 19) * ((3 * k + 8) * 2) := by rw [h8]; ring
      _ ≤ 3 ^ (2 * k ^ 2 + 12 * k + 17) := aux_typeB k
    exact lt_irrefl _ this

theorem lieOdd_typeC {q m e h g X : ℕ} (hq : 3 ≤ q) (hqodd : Odd q) (hm : 4 ≤ m)
    (hX : TwoPartBound X (q ^ (m - 1) * (q - 1)) ((q + 1) * ordProj[2] m))
    (heq : q ^ (m * (m - 1)) * (X * ∏ i ∈ Icc 1 (m - 1), (q ^ (2 * i) - 1)) = 2 ^ e * h * g)
    (hg : g ≤ 4) (he1 : 1 ≤ e) (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  have hb := twoPartBound_omega hq hqodd (by omega) hX
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
  simp only [show k + 4 - 1 = k + 3 by omega] at hb heq
  have hb' : TwoPartBound (X * ∏ i ∈ Icc 1 (k + 3), (q ^ (2 * i) - 1))
      (q ^ ((k + 4) * (k + 3)) * (q - 1) ^ (k + 4)) ((q + 1) ^ (k + 4) * 2 ^ (2 * k + 6)) := by
    refine hb.mono le_rfl ?_
    have := ordProj_two_factorial_le (m := k + 3 + 1) (by omega)
    simp only [Nat.add_sub_cancel] at this
    calc (q + 1) ^ (k + 4) * 2 ^ (k + 3) * ordProj[2] (k + 4).factorial
        ≤ (q + 1) ^ (k + 4) * 2 ^ (k + 3) * 2 ^ (k + 3) := Nat.mul_le_mul_left _ this
      _ = (q + 1) ^ (k + 4) * 2 ^ (2 * k + 6) := by ring
  have hc := lt_of_twoPartBound hq hqodd heq hb' hg he1 hdiv
    (M := 2 * k ^ 2 + 13 * k + 19) (by ring)
  have h8 : (8 : ℕ) ^ (k + 4) * 4 ^ (2 * k + 6) = 2 ^ (7 * k + 24) := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul,
      ← pow_mul, ← pow_add]
    ring_nf
  have := calc 3 ^ (2 * k ^ 2 + 14 * k + 23)
      = 3 ^ (k + 4) * 3 ^ (2 * k ^ 2 + 13 * k + 19) := by ring
    _ ≤ 3 ^ (k + 4) * q ^ (2 * k ^ 2 + 13 * k + 19) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hq _)
    _ < 8 ^ (k + 4) * 4 ^ (2 * k + 6) * (k + 4 + (2 * k + 6)) * 4 := hc
    _ = 2 ^ (7 * k + 24) * ((3 * k + 10) * 4) := by rw [h8]; ring
    _ ≤ 3 ^ (2 * k ^ 2 + 14 * k + 23) := aux_typeC k
  exact lt_irrefl _ this

end CFSG.SeitzReduction.RankOne.LieOdd
