module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrderArith

public section

namespace CFSG.OddStandard.AltStdSec

open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
  CFSG.Assembly.LowTwoRank

theorem cof_prod_le (q : ℕ) (s : Finset ℕ) (F g : ℕ → ℕ) (h : ∀ i ∈ s, F i ≤ q ^ g i) :
    ∏ i ∈ s, F i ≤ q ^ (∑ i ∈ s, g i) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod h

theorem cof_pow_add_one_le {q : ℕ} (hq : 2 ≤ q) (i : ℕ) : q ^ i + 1 ≤ q ^ (i + 1) := by
  have h1 : 1 ≤ q ^ i := Nat.one_le_pow _ _ (by omega)
  calc q ^ i + 1 ≤ q ^ i * q := by nlinarith
    _ = q ^ (i + 1) := (pow_succ _ _).symm

theorem cof_two_mul_half (n : ℕ) : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
  Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)

theorem cof_two_le_pow {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f) :
    2 ≤ p ^ f :=
  hadm.1.two_le.trans (Nat.le_self_pow (by have := hadm.2.1; omega) p)

theorem cof_sum_id_le {n : ℕ} (hn : 2 ≤ n) : ∑ i ∈ Finset.Icc 2 n, i ≤ n * (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at ih ⊢
    nlinarith

theorem cof_sum_psu_le {n : ℕ} (hn : 3 ≤ n) :
    ∑ i ∈ Finset.Icc 2 n, (if Even i then i else i + 1) ≤ n * (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h : (if Even (k + 1) then k + 1 else k + 1 + 1) ≤ k + 2 := by split_ifs <;> omega
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at ih ⊢
    nlinarith

theorem cof_sum_two_mul (m : ℕ) : ∑ i ∈ Finset.Icc 1 m, 2 * i = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

theorem cof_prod_two_mul_le (q m : ℕ) :
    ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) ≤ q ^ (m * (m + 1)) := by
  rw [← cof_sum_two_mul]
  exact cof_prod_le q _ _ _ fun i _ => Nat.sub_le _ _

theorem cof_PSL_le {n q : ℕ} (hq : 2 ≤ q) (hn : 2 ≤ n) :
    lieOrderCofactor .PSL n q ≤ q ^ (2 * lieSylowExponent .PSL n) := by
  simp only [lieOrderCofactor, lieSylowExponent, cof_two_mul_half]
  exact (cof_prod_le q _ _ id fun i _ => Nat.sub_le _ _).trans
    (Nat.pow_le_pow_right (by omega) (cof_sum_id_le hn))

theorem cof_PSU_le {n q : ℕ} (hq : 2 ≤ q) (hn : 3 ≤ n) :
    lieOrderCofactor .PSU n q ≤ q ^ (2 * lieSylowExponent .PSU n) := by
  simp only [lieOrderCofactor, lieSylowExponent, cof_two_mul_half]
  refine (cof_prod_le q _ _ (fun i => if Even i then i else i + 1) fun i _ => ?_).trans
    (Nat.pow_le_pow_right (by omega) (cof_sum_psu_le hn))
  split_ifs
  · exact Nat.sub_le _ _
  · exact cof_pow_add_one_le hq i

theorem cof_PSp_le {n q : ℕ} (hq : 2 ≤ q) (hn : 2 ≤ n) :
    lieOrderCofactor .PSp n q ≤ q ^ (2 * lieSylowExponent .PSp n) := by
  simp only [lieOrderCofactor, lieSylowExponent]
  exact (cof_prod_two_mul_le q n).trans (Nat.pow_le_pow_right (by omega) (by nlinarith))

theorem cof_POmegaOdd_le {n q : ℕ} (hq : 2 ≤ q) (hn : 3 ≤ n) :
    lieOrderCofactor .POmegaOdd n q ≤ q ^ (2 * lieSylowExponent .POmegaOdd n) := by
  simp only [lieOrderCofactor, lieSylowExponent]
  exact (cof_prod_two_mul_le q n).trans (Nat.pow_le_pow_right (by omega) (by nlinarith))

theorem cof_POmegaPlus_le {n q : ℕ} (hq : 2 ≤ q) (hn : 4 ≤ n) :
    lieOrderCofactor .POmegaPlus n q ≤ q ^ (2 * lieSylowExponent .POmegaPlus n) := by
  simp only [lieOrderCofactor, lieSylowExponent]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  calc (q ^ (k + 1) - 1) * ∏ i ∈ Finset.Icc 1 k, (q ^ (2 * i) - 1)
      ≤ q ^ (k + 1) * q ^ (k * (k + 1)) :=
        Nat.mul_le_mul (Nat.sub_le _ _) (cof_prod_two_mul_le q k)
    _ = q ^ (k + 1 + k * (k + 1)) := (pow_add _ _ _).symm
    _ ≤ q ^ (2 * ((k + 1) * k)) := Nat.pow_le_pow_right (by omega) (by nlinarith)

theorem cof_POmegaMinus_le {n q : ℕ} (hq : 2 ≤ q) (hn : 4 ≤ n) :
    lieOrderCofactor .POmegaMinus n q ≤ q ^ (2 * lieSylowExponent .POmegaMinus n) := by
  simp only [lieOrderCofactor, lieSylowExponent]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  calc (q ^ (k + 1) + 1) * ∏ i ∈ Finset.Icc 1 k, (q ^ (2 * i) - 1)
      ≤ q ^ (k + 1 + 1) * q ^ (k * (k + 1)) :=
        Nat.mul_le_mul (cof_pow_add_one_le hq _) (cof_prod_two_mul_le q k)
    _ = q ^ (k + 1 + 1 + k * (k + 1)) := (pow_add _ _ _).symm
    _ ≤ q ^ (2 * ((k + 1) * k)) := Nat.pow_le_pow_right (by omega) (by nlinarith)

theorem cof_G2_le {n q : ℕ} (hq : 2 ≤ q) :
    lieOrderCofactor .G2 n q ≤ q ^ (2 * lieSylowExponent .G2 n) := by
  simp only [lieOrderCofactor, lieSylowExponent]
  calc (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 6 * q ^ 2 := by gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 8 := by ring
    _ ≤ q ^ (2 * 6) := Nat.pow_le_pow_right (by omega) (by norm_num)

theorem cof_F4_le {n q : ℕ} (hq : 2 ≤ q) :
    lieOrderCofactor .F4 n q ≤ q ^ (2 * lieSylowExponent .F4 n) := by
  simp only [lieOrderCofactor, lieSylowExponent]
  calc (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
      ≤ q ^ 12 * q ^ 8 * q ^ 6 * q ^ 2 := by gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 28 := by ring
    _ ≤ q ^ (2 * 24) := Nat.pow_le_pow_right (by omega) (by norm_num)

theorem cof_E6_le {n q : ℕ} (hq : 2 ≤ q) :
    lieOrderCofactor .E6 n q ≤ q ^ (2 * lieSylowExponent .E6 n) := by
  simp only [lieOrderCofactor, lieSylowExponent]
  calc (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1)
      ≤ q ^ 12 * q ^ 9 * q ^ 8 * q ^ 6 * q ^ 5 * q ^ 2 := by gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 42 := by ring
    _ ≤ q ^ (2 * 36) := Nat.pow_le_pow_right (by omega) (by norm_num)

theorem cof_E7_le {n q : ℕ} (hq : 2 ≤ q) :
    lieOrderCofactor .E7 n q ≤ q ^ (2 * lieSylowExponent .E7 n) := by
  simp only [lieOrderCofactor, lieSylowExponent]
  calc (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
        (q ^ 2 - 1)
      ≤ q ^ 18 * q ^ 14 * q ^ 12 * q ^ 10 * q ^ 8 * q ^ 6 * q ^ 2 := by
        gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 70 := by ring
    _ ≤ q ^ (2 * 63) := Nat.pow_le_pow_right (by omega) (by norm_num)

theorem cof_E8_le {n q : ℕ} (hq : 2 ≤ q) :
    lieOrderCofactor .E8 n q ≤ q ^ (2 * lieSylowExponent .E8 n) := by
  simp only [lieOrderCofactor, lieSylowExponent]
  calc (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) *
        (q ^ 8 - 1) * (q ^ 2 - 1)
      ≤ q ^ 30 * q ^ 24 * q ^ 20 * q ^ 18 * q ^ 14 * q ^ 12 * q ^ 8 * q ^ 2 := by
        gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 128 := by ring
    _ ≤ q ^ (2 * 120) := Nat.pow_le_pow_right (by omega) (by norm_num)

theorem cof_twistedE6_le {n q : ℕ} (hq : 2 ≤ q) :
    lieOrderCofactor .twistedE6 n q ≤ q ^ (2 * lieSylowExponent .twistedE6 n) := by
  simp only [lieOrderCofactor, lieSylowExponent]
  have h9 : q ^ 9 + 1 ≤ q ^ 10 := cof_pow_add_one_le hq 9
  have h5 : q ^ 5 + 1 ≤ q ^ 6 := cof_pow_add_one_le hq 5
  calc (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1)
      ≤ q ^ 12 * q ^ 10 * q ^ 8 * q ^ 6 * q ^ 6 * q ^ 2 := by gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 44 := by ring
    _ ≤ q ^ (2 * 36) := Nat.pow_le_pow_right (by omega) (by norm_num)

theorem cof_triality_le {q : ℕ} (hq : 2 ≤ q) : q ^ 8 + q ^ 4 + 1 ≤ q ^ 9 := by
  have h4 : 2 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
  have h8 : q ^ 8 = q ^ 4 * q ^ 4 := by ring
  have h9 : q ^ 9 = q ^ 8 * q := by ring
  nlinarith

theorem cof_trialityD4_le {n q : ℕ} (hq : 2 ≤ q) :
    lieOrderCofactor .trialityD4 n q ≤ q ^ (2 * lieSylowExponent .trialityD4 n) := by
  simp only [lieOrderCofactor, lieSylowExponent]
  have h := cof_triality_le hq
  calc (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 9 * q ^ 6 * q ^ 2 := by
        gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 17 := by ring
    _ ≤ q ^ (2 * 12) := Nat.pow_le_pow_right (by omega) (by norm_num)

theorem cof_twistedB2_le {n q : ℕ} (hq : 2 ≤ q) :
    lieOrderCofactor .twistedB2 n q ≤ q ^ (2 * lieSylowExponent .twistedB2 n) := by
  simp only [lieOrderCofactor, lieSylowExponent]
  have h2 : q ^ 2 + 1 ≤ q ^ 3 := cof_pow_add_one_le hq 2
  calc (q ^ 2 + 1) * (q - 1) ≤ q ^ 3 * q := Nat.mul_le_mul h2 (Nat.sub_le _ _)
    _ = q ^ (2 * 2) := by ring

theorem cof_twistedG2_le {n q : ℕ} (hq : 2 ≤ q) :
    lieOrderCofactor .twistedG2 n q ≤ q ^ (2 * lieSylowExponent .twistedG2 n) := by
  simp only [lieOrderCofactor, lieSylowExponent]
  have h3 : q ^ 3 + 1 ≤ q ^ 4 := cof_pow_add_one_le hq 3
  calc (q ^ 3 + 1) * (q - 1) ≤ q ^ 4 * q := Nat.mul_le_mul h3 (Nat.sub_le _ _)
    _ = q ^ 5 := by ring
    _ ≤ q ^ (2 * 3) := Nat.pow_le_pow_right (by omega) (by norm_num)

theorem cof_twistedF4_le {n q : ℕ} (hq : 2 ≤ q) :
    lieOrderCofactor .twistedF4 n q ≤ q ^ (2 * lieSylowExponent .twistedF4 n) := by
  simp only [lieOrderCofactor, lieSylowExponent]
  have h6 : q ^ 6 + 1 ≤ q ^ 7 := cof_pow_add_one_le hq 6
  have h3 : q ^ 3 + 1 ≤ q ^ 4 := cof_pow_add_one_le hq 3
  calc (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) ≤ q ^ 7 * q ^ 4 * q ^ 4 * q := by
        gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 16 := by ring
    _ ≤ q ^ (2 * 12) := Nat.pow_le_pow_right (by omega) (by norm_num)

theorem lieOrderCofactor_le {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f) :
    lieOrderCofactor t n (p ^ f) ≤ (p ^ f) ^ (2 * lieSylowExponent t n) := by
  have hq := cof_two_le_pow hadm
  cases t
  case PSL => obtain ⟨-, -, hn, -⟩ := hadm; exact cof_PSL_le hq hn
  case PSU => obtain ⟨-, -, hn, -⟩ := hadm; exact cof_PSU_le hq hn
  case PSp => obtain ⟨-, -, hn, -⟩ := hadm; exact cof_PSp_le hq hn
  case POmegaOdd => obtain ⟨-, -, hn, -⟩ := hadm; exact cof_POmegaOdd_le hq hn
  case POmegaPlus => obtain ⟨-, -, hn⟩ := hadm; exact cof_POmegaPlus_le hq hn
  case POmegaMinus => obtain ⟨-, -, hn⟩ := hadm; exact cof_POmegaMinus_le hq hn
  case G2 => exact cof_G2_le hq
  case F4 => exact cof_F4_le hq
  case E6 => exact cof_E6_le hq
  case E7 => exact cof_E7_le hq
  case E8 => exact cof_E8_le hq
  case twistedE6 => exact cof_twistedE6_le hq
  case trialityD4 => exact cof_trialityD4_le hq
  case twistedB2 => exact cof_twistedB2_le hq
  case twistedG2 => exact cof_twistedG2_le hq
  case twistedF4 => exact cof_twistedF4_le hq
  case Tits =>
    obtain ⟨-, -, -, rfl, rfl⟩ := hadm
    norm_num [lieOrderCofactor, lieSylowExponent]

end CFSG.OddStandard.AltStdSec
