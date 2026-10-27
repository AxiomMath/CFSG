module

public import CFSG.LocalAnalysis.SeitzReduction.CrossCharEven
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharOdd
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof (lieOrderCofactor lieOrderNumerator_eq)
open CFSG.SeitzReduction.CrossChar
open Finset

@[expose] def cofE : StatedLieTag → ℕ → ℕ
  | .PSL, n => n * (n - 1) / 2 + n - 1
  | .PSU, n => n * (n - 1) / 2 + n - 1
  | .PSp, n => n * (n + 1)
  | .POmegaOdd, n => n * (n + 1)
  | .POmegaPlus, n => n + (n - 1) * (n - 1 + 1)
  | .POmegaMinus, n => n + 1 + (n - 1) * (n - 1 + 1)
  | .G2, _ => 8
  | .F4, _ => 28
  | .E6, _ => 42
  | .E7, _ => 70
  | .E8, _ => 128
  | .twistedE6, _ => 44
  | .trialityD4, _ => 17
  | .twistedB2, _ => 3
  | .twistedG2, _ => 4
  | .twistedF4, _ => 14
  | .Tits, _ => 14

theorem pow_add_one_le_pow_succ' {q : ℕ} (hq : 2 ≤ q) (d : ℕ) : q ^ d + 1 ≤ q ^ (d + 1) := by
  rw [pow_succ]
  have := Nat.one_le_pow d q (by omega)
  nlinarith

theorem cof_lt_pow {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f) :
    lieOrderCofactor t n (2 ^ f) < (2 ^ f) ^ cofE t n := by
  have hf : 1 ≤ f := hadm.2.1
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hq1 : 1 ≤ 2 ^ f := by omega
  set q := 2 ^ f with hqdef
  cases t
  case PSL =>
    obtain ⟨-, -, hn, -, -⟩ := hadm
    exact prod_Icc_two_sub_one_lt hq1 hn
  case PSU =>
    obtain ⟨-, -, hn, -⟩ := hadm
    exact prod_psu_lt hq (by omega)
  case PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    exact prod_Icc_one_sub_one_lt hq1 (by omega)
  case POmegaOdd => exact absurd rfl hadm.2.2.2
  case POmegaPlus =>
    obtain ⟨-, -, hn⟩ := hadm
    have hP := prod_Icc_one_sub_one_lt hq1 (by omega : 1 ≤ n - 1)
    show (q ^ n - 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1) < q ^ (n + (n - 1) * (n - 1 + 1))
    rw [pow_add]
    exact Nat.mul_lt_mul'' (pow_sub_one_lt_pow hq1 n) hP
  case POmegaMinus =>
    obtain ⟨-, -, hn⟩ := hadm
    have hP := prod_Icc_one_sub_one_lt hq1 (by omega : 1 ≤ n - 1)
    have hX : q ^ n + 1 ≤ q ^ (n + 1) := pow_add_one_le_pow_succ' hq n
    show (q ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1) <
      q ^ (n + 1 + (n - 1) * (n - 1 + 1))
    rw [pow_add]
    exact Nat.mul_lt_mul_of_le_of_lt hX hP (by positivity)
  case G2 =>
    show (q ^ 6 - 1) * (q ^ 2 - 1) < q ^ 8
    calc (q ^ 6 - 1) * (q ^ 2 - 1) < q ^ 6 * q ^ 2 :=
          Nat.mul_lt_mul'' (pow_sub_one_lt_pow hq1 6) (pow_sub_one_lt_pow hq1 2)
      _ = q ^ 8 := by ring
  case F4 =>
    show (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1) < q ^ 28
    calc (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
        < q ^ 12 * q ^ 8 * q ^ 6 * q ^ 2 :=
          Nat.mul_lt_mul'' (Nat.mul_lt_mul'' (Nat.mul_lt_mul'' (pow_sub_one_lt_pow hq1 12)
            (pow_sub_one_lt_pow hq1 8)) (pow_sub_one_lt_pow hq1 6)) (pow_sub_one_lt_pow hq1 2)
      _ = q ^ 28 := by ring
  case E6 =>
    show (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1) <
      q ^ 42
    calc (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1)
        < q ^ 12 * q ^ 9 * q ^ 8 * q ^ 6 * q ^ 5 * q ^ 2 :=
          Nat.mul_lt_mul'' (Nat.mul_lt_mul'' (Nat.mul_lt_mul'' (Nat.mul_lt_mul''
            (Nat.mul_lt_mul'' (pow_sub_one_lt_pow hq1 12) (pow_sub_one_lt_pow hq1 9))
            (pow_sub_one_lt_pow hq1 8)) (pow_sub_one_lt_pow hq1 6))
            (pow_sub_one_lt_pow hq1 5)) (pow_sub_one_lt_pow hq1 2)
      _ = q ^ 42 := by ring
  case E7 =>
    show (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
      (q ^ 6 - 1) * (q ^ 2 - 1) < q ^ 70
    calc (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
          (q ^ 6 - 1) * (q ^ 2 - 1)
        < q ^ 18 * q ^ 14 * q ^ 12 * q ^ 10 * q ^ 8 * q ^ 6 * q ^ 2 :=
          Nat.mul_lt_mul'' (Nat.mul_lt_mul'' (Nat.mul_lt_mul'' (Nat.mul_lt_mul''
            (Nat.mul_lt_mul'' (Nat.mul_lt_mul'' (pow_sub_one_lt_pow hq1 18)
              (pow_sub_one_lt_pow hq1 14)) (pow_sub_one_lt_pow hq1 12))
            (pow_sub_one_lt_pow hq1 10)) (pow_sub_one_lt_pow hq1 8))
            (pow_sub_one_lt_pow hq1 6)) (pow_sub_one_lt_pow hq1 2)
      _ = q ^ 70 := by ring
  case E8 =>
    show (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) *
      (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1) < q ^ 128
    calc (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) *
          (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)
        < q ^ 30 * q ^ 24 * q ^ 20 * q ^ 18 * q ^ 14 * q ^ 12 * q ^ 8 * q ^ 2 :=
          Nat.mul_lt_mul'' (Nat.mul_lt_mul'' (Nat.mul_lt_mul'' (Nat.mul_lt_mul''
            (Nat.mul_lt_mul'' (Nat.mul_lt_mul'' (Nat.mul_lt_mul'' (pow_sub_one_lt_pow hq1 30)
              (pow_sub_one_lt_pow hq1 24)) (pow_sub_one_lt_pow hq1 20))
              (pow_sub_one_lt_pow hq1 18)) (pow_sub_one_lt_pow hq1 14))
            (pow_sub_one_lt_pow hq1 12)) (pow_sub_one_lt_pow hq1 8)) (pow_sub_one_lt_pow hq1 2)
      _ = q ^ 128 := by ring
  case twistedE6 =>
    show (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1) <
      q ^ 44
    have h9 := pow_add_one_le_pow_succ' hq 9
    have h5 := pow_add_one_le_pow_succ' hq 5
    calc (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1)
        < q ^ 12 * q ^ 10 * q ^ 8 * q ^ 6 * q ^ 6 * q ^ 2 :=
          Nat.mul_lt_mul_of_le_of_lt (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
            (Nat.mul_le_mul (Nat.sub_le _ _) h9) (Nat.sub_le _ _))
            (Nat.sub_le _ _)) h5) (pow_sub_one_lt_pow hq1 2) (by positivity)
      _ = q ^ 44 := by ring
  case trialityD4 =>
    show (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) < q ^ 17
    have h4 : q ^ 4 + 1 ≤ q ^ 8 := by
      have : q ^ 4 + 1 ≤ q ^ 5 := pow_add_one_le_pow_succ' hq 4
      exact this.trans (Nat.pow_le_pow_right (by omega) (by norm_num))
    have h8 : q ^ 8 + q ^ 4 + 1 ≤ q ^ 9 := by
      have : q ^ 8 + 1 ≤ q ^ 9 := pow_add_one_le_pow_succ' hq 8
      nlinarith [Nat.one_le_pow 8 q (by omega)]
    calc (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) < q ^ 9 * q ^ 6 * q ^ 2 :=
          Nat.mul_lt_mul_of_le_of_lt (Nat.mul_le_mul h8 (Nat.sub_le _ _))
            (pow_sub_one_lt_pow hq1 2) (by positivity)
      _ = q ^ 17 := by ring
  case twistedB2 =>
    obtain ⟨-, -, -, -, -, hf3⟩ := hadm
    have hq8 : 8 ≤ q := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
    show (q ^ 2 + 1) * (q - 1) < q ^ 3
    have h1 : q - 1 + 1 = q := by omega
    have h2 : (q ^ 2 + 1) * (q - 1) + q ^ 2 = q ^ 3 + (q - 1) := by
      rw [← h1]; simp only [Nat.add_sub_cancel]; ring
    have h3 : q - 1 < q ^ 2 := by nlinarith
    omega
  case twistedG2 => exact absurd hadm.2.2.2.1 (by norm_num)
  case twistedF4 =>
    show (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) < q ^ 14
    have h1 : (q ^ 4 - 1) * (q ^ 6 + 1) < q ^ 10 := by
      have h4 := Nat.one_le_pow 4 q hq1
      have h6 : q ^ 4 < q ^ 6 + 1 := by
        have : q ^ 4 ≤ q ^ 6 := Nat.pow_le_pow_right hq1 (by norm_num)
        omega
      zify [h4]
      have : (q : ℤ) ^ 10 = (q : ℤ) ^ 4 * (q : ℤ) ^ 6 := by ring
      nlinarith
    have h2 : (q - 1) * (q ^ 3 + 1) < q ^ 4 := by
      have h3 : 1 ≤ q := hq1
      have h6 : q < q ^ 3 + 1 := by
        have : q ≤ q ^ 3 := by
          calc q = q ^ 1 := (pow_one q).symm
            _ ≤ q ^ 3 := Nat.pow_le_pow_right hq1 (by norm_num)
        omega
      zify [h3]
      have : (q : ℤ) ^ 4 = (q : ℤ) * (q : ℤ) ^ 3 := by ring
      nlinarith
    calc (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1)
        = ((q ^ 4 - 1) * (q ^ 6 + 1)) * ((q - 1) * (q ^ 3 + 1)) := by ring
      _ < q ^ 10 * q ^ 4 := Nat.mul_lt_mul'' h1 h2
      _ = q ^ 14 := by ring
  case Tits =>
    obtain ⟨-, -, -, -, rfl⟩ := hadm
    show (8775 : ℕ) < (2 ^ 1) ^ 14
    norm_num

open CFSG.ComponentClassification.CatLeafProof (lieOrderDivisor_ne_zero not_dvd_lieOrderDivisor
  lieOrderCofactor_coprime)

theorem univ_of_cof {q N E C M D : ℕ} (hq : 2 ≤ q) (hD : 1 ≤ D) (hM : M * D = q ^ N * C)
    (hC : C < q ^ E) (hE : 2 * E ≤ 3 * N) : M ^ 2 < (q ^ N) ^ 5 := by
  have h1 : M < q ^ (N + E) := by
    calc M ≤ M * D := Nat.le_mul_of_pos_right M hD
      _ = q ^ N * C := hM
      _ < q ^ N * q ^ E := Nat.mul_lt_mul_of_pos_left hC (by positivity)
      _ = q ^ (N + E) := (pow_add q N E).symm
  calc M ^ 2 < (q ^ (N + E)) ^ 2 := Nat.pow_lt_pow_left h1 (by norm_num)
    _ = q ^ (2 * N + 2 * E) := by rw [← pow_mul]; ring_nf
    _ ≤ q ^ (5 * N) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = (q ^ N) ^ 5 := by rw [← pow_mul]; ring_nf

theorem cofE_le {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hne : ¬ ((t = .PSL ∧ (n = 2 ∨ n = 3)) ∨ (t = .PSU ∧ n = 3))) :
    2 * cofE t n ≤ 3 * lieSylowExponent t n := by
  cases t
  case PSL =>
    obtain ⟨-, -, hn, -, -⟩ := hadm
    have h4 : 4 ≤ n := by
      by_contra hlt
      exact hne (Or.inl ⟨rfl, by omega⟩)
    have h2N := two_mul_tri n
    have : 4 * (n - 1) ≤ n * (n - 1) := Nat.mul_le_mul_right _ h4
    simp only [cofE, lieSylowExponent]
    omega
  case PSU =>
    obtain ⟨-, -, hn, -⟩ := hadm
    have h4 : 4 ≤ n := by
      by_contra hlt
      exact hne (Or.inr ⟨rfl, by omega⟩)
    have h2N := two_mul_tri n
    have : 4 * (n - 1) ≤ n * (n - 1) := Nat.mul_le_mul_right _ h4
    simp only [cofE, lieSylowExponent]
    omega
  case PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    simp only [cofE, lieSylowExponent]
    nlinarith
  case POmegaOdd => exact absurd rfl hadm.2.2.2
  case POmegaPlus =>
    obtain ⟨-, -, hn⟩ := hadm
    simp only [cofE, lieSylowExponent]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    simp only [show k + 4 - 1 = k + 3 by omega]
    nlinarith
  case POmegaMinus =>
    obtain ⟨-, -, hn⟩ := hadm
    simp only [cofE, lieSylowExponent]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    simp only [show k + 4 - 1 = k + 3 by omega]
    nlinarith
  case twistedG2 => exact absurd hadm.2.2.2.1 (by norm_num)
  all_goals simp [cofE, lieSylowExponent]

theorem univ_lt {t : StatedLieTag} {n f M : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hne : ¬ ((t = .PSL ∧ (n = 2 ∨ n = 3)) ∨ (t = .PSU ∧ n = 3)))
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f)) :
    M ^ 2 < (2 ^ (lieSylowExponent t n * f)) ^ 5 := by
  have hf : 1 ≤ f := hadm.2.1
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hD : 1 ≤ lieOrderDivisor t n (2 ^ f) :=
    Nat.one_le_iff_ne_zero.mpr (lieOrderDivisor_ne_zero hadm)
  rw [lieOrderNumerator_eq hadm] at hM
  have h := univ_of_cof hq hD hM (cof_lt_pow hadm) (cofE_le hadm hne)
  have e : 2 ^ (lieSylowExponent t n * f) = (2 ^ f) ^ lieSylowExponent t n := by
    rw [← pow_mul, mul_comm]
  rw [e]
  exact h

end CFSG.LocalAnalysis.GLTheoremA.HDesc
