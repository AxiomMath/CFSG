module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrderArith
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eZsig
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P58b.OLie

open CFSG CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.HarrisLit.T1.P51e (IsPrimDiv exists_isPrimDiv)

theorem exists_witness_index (hO : LieOrderFormulasInput) {Y : Type} [Group Y]
    {τ : StatedLieTag} {n p e : ℕ} (hp2 : p ≠ 2) (he2 : 2 ≤ e)
    (hadm : StatedLieAdmissible τ n p e) (hY : Blueprint.LieModel Y τ n p e) :
    ∃ D ℓ : ℕ, 2 ≤ D ∧ IsPrimDiv ℓ p (e * D) ∧ ℓ ∣ Nat.card Y ∧
      2 * lieSylowExponent τ n ≤ D * (D - 1) ∧
      (2 * lieSylowExponent τ n = D * (D - 1) → τ = .PSL ∧ n = D) := by
  obtain ⟨-, hord, -⟩ := hO Y τ n p e hadm hY
  have hp : p.Prime := hadm.1
  have hp0 : 0 < p := hp.pos
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  rw [lieOrderNumerator_eq hadm] at hord
  have htr : ∀ {D ℓ : ℕ}, IsPrimDiv ℓ p (e * D) → ℓ ∣ lieOrderCofactor τ n (p ^ e) →
      ¬ ℓ ∣ lieOrderDivisor τ n (p ^ e) → ℓ ∣ Nat.card Y := by
    intro D ℓ hℓ hc hdiv
    have h1 : ℓ ∣ Nat.card Y * lieOrderDivisor τ n (p ^ e) := by
      rw [hord]
      exact Dvd.dvd.mul_left hc _
    exact ((Nat.Prime.dvd_mul hℓ.1).1 h1).resolve_right hdiv
  have hsub : ∀ {D ℓ c : ℕ}, IsPrimDiv ℓ p (e * D) → 2 ≤ D → c ∣ p ^ e - 1 → ¬ ℓ ∣ c :=
    fun {D ℓ c} hℓ hD hc hd => hℓ.not_dvd_pow_sub_one hp0 (by positivity)
      (fun h => by
        have := Nat.le_of_dvd (by omega) h
        nlinarith) (hd.trans hc)
  have hsmall : ∀ {D ℓ c : ℕ}, IsPrimDiv ℓ p (e * D) → 2 ≤ D → 0 < c → c ≤ 4 → ¬ ℓ ∣ c :=
    fun {D ℓ c} hℓ hD hc0 hc4 => hℓ.not_dvd_small hp0 (by nlinarith) hc0 hc4
  cases τ with
  | PSL =>
    obtain ⟨-, -, hn, -, -⟩ := hadm
    obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ e * n by nlinarith)
    refine ⟨n, ℓ, hn, hℓ, htr hℓ ?_ ?_, ?_, fun _ => ⟨rfl, rfl⟩⟩
    · exact hℓ.dvd_pow_pow_sub_one.trans
        (Finset.dvd_prod_of_mem (fun i => (p ^ e) ^ i - 1) (Finset.mem_Icc.2 ⟨hn, le_rfl⟩))
    · exact hsub hℓ hn (Nat.gcd_dvd_right _ _)
    · change 2 * (n * (n - 1) / 2) ≤ n * (n - 1)
      omega
  | PSU =>
    obtain ⟨-, -, hn, -⟩ := hadm
    obtain ⟨i, hi, hin, hodd⟩ : ∃ i, 3 ≤ i ∧ i ≤ n ∧ n ≤ i + 1 ∧ ¬ Even i := by
      rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
      · exact ⟨n - 1, by omega, by omega, by omega, fun ⟨k, hk⟩ => by omega⟩
      · exact ⟨n, by omega, le_rfl, by omega, fun ⟨k, hk⟩ => by omega⟩
    obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ e * (2 * i) by nlinarith)
    have hℓ' : IsPrimDiv ℓ p (2 * (e * i)) := by
      rw [show 2 * (e * i) = e * (2 * i) by ring]
      exact hℓ
    refine ⟨2 * i, ℓ, by omega, hℓ, htr hℓ ?_ ?_, ?_, fun h => ?_⟩
    · refine (hℓ'.dvd_pow_pow_add_one (by positivity)).trans ?_
      change (p ^ e) ^ i + 1 ∣ ∏ j ∈ Finset.Icc 2 n,
        (if Even j then (p ^ e) ^ j - 1 else (p ^ e) ^ j + 1)
      have hmem : i ∈ Finset.Icc 2 n := Finset.mem_Icc.2 ⟨by omega, hin⟩
      have h := Finset.dvd_prod_of_mem
        (fun j => if Even j then (p ^ e) ^ j - 1 else (p ^ e) ^ j + 1) hmem
      simpa [hodd] using h
    · intro hd
      have h1 : ℓ ∣ p ^ e + 1 := hd.trans (Nat.gcd_dvd_right _ _)
      have h2 := hℓ.dvd_two_mul_of_dvd_add_one hp0 (by positivity) h1
      have := Nat.le_of_dvd (by omega) h2
      nlinarith
    · change 2 * (n * (n - 1) / 2) ≤ 2 * i * (2 * i - 1)
      have : 2 * (n * (n - 1) / 2) ≤ n * (n - 1) := Nat.mul_div_le _ _
      have h2 : n * (n - 1) ≤ 2 * i * (2 * i - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    · exfalso
      change 2 * (n * (n - 1) / 2) = 2 * i * (2 * i - 1) at h
      have : 2 * (n * (n - 1) / 2) ≤ n * (n - 1) := Nat.mul_div_le _ _
      have h2 : n * (n - 1) < 2 * i * (2 * i - 1) := by
        have h3 : n + 1 ≤ 2 * i := by omega
        calc n * (n - 1) < (n + 1) * n := by
              rcases n with _ | n
              · omega
              · simp only [Nat.add_sub_cancel]; nlinarith
          _ ≤ 2 * i * (2 * i - 1) := Nat.mul_le_mul h3 (by omega)
      omega
  | PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ e * (2 * n) by nlinarith)
    refine ⟨2 * n, ℓ, by omega, hℓ, htr hℓ ?_ ?_, ?_, fun h => ?_⟩
    · exact hℓ.dvd_pow_pow_sub_one.trans (Finset.dvd_prod_of_mem
        (fun i => (p ^ e) ^ (2 * i) - 1) (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩))
    · exact hsmall hℓ (by omega) (Nat.gcd_pos_of_pos_left _ two_pos)
        (le_trans (Nat.gcd_le_left _ two_pos) (by norm_num))
    · change 2 * n ^ 2 ≤ 2 * n * (2 * n - 1)
      have : n ^ 2 ≤ n * (2 * n - 1) := by rw [sq]; exact Nat.mul_le_mul le_rfl (by omega)
      nlinarith
    · exfalso
      change 2 * n ^ 2 = 2 * n * (2 * n - 1) at h
      have : n * n < n * (2 * n - 1) := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      nlinarith
  | POmegaOdd =>
    obtain ⟨-, -, hn, -⟩ := hadm
    obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ e * (2 * n) by nlinarith)
    refine ⟨2 * n, ℓ, by omega, hℓ, htr hℓ ?_ ?_, ?_, fun h => ?_⟩
    · exact hℓ.dvd_pow_pow_sub_one.trans (Finset.dvd_prod_of_mem
        (fun i => (p ^ e) ^ (2 * i) - 1) (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩))
    · change ¬ ℓ ∣ 2
      exact hsmall hℓ (by omega) two_pos (by norm_num)
    · change 2 * n ^ 2 ≤ 2 * n * (2 * n - 1)
      have : n ^ 2 ≤ n * (2 * n - 1) := by rw [sq]; exact Nat.mul_le_mul le_rfl (by omega)
      nlinarith
    · exfalso
      change 2 * n ^ 2 = 2 * n * (2 * n - 1) at h
      have : n * n < n * (2 * n - 1) := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      nlinarith
  | POmegaPlus =>
    obtain ⟨-, -, hn⟩ := hadm
    obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ e * (2 * (n - 1)) by
      have : 3 ≤ n - 1 := by omega
      nlinarith)
    refine ⟨2 * (n - 1), ℓ, by omega, hℓ, htr hℓ ?_ ?_, ?_, fun h => ?_⟩
    · refine Dvd.dvd.mul_left (hℓ.dvd_pow_pow_sub_one.trans (Finset.dvd_prod_of_mem
        (fun i => (p ^ e) ^ (2 * i) - 1) (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩))) _
    · exact hsmall hℓ (by omega) (Nat.gcd_pos_of_pos_left _ (by norm_num))
        (Nat.gcd_le_left _ (by norm_num))
    · change 2 * (n * (n - 1)) ≤ 2 * (n - 1) * (2 * (n - 1) - 1)
      have : n ≤ 2 * (n - 1) - 1 := by omega
      have := Nat.mul_le_mul_left (n - 1) this
      nlinarith
    · exfalso
      change 2 * (n * (n - 1)) = 2 * (n - 1) * (2 * (n - 1) - 1) at h
      have : (n - 1) * n < (n - 1) * (2 * (n - 1) - 1) :=
        Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      nlinarith
  | POmegaMinus =>
    obtain ⟨-, -, hn⟩ := hadm
    obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ e * (2 * n) by nlinarith)
    have hℓ' : IsPrimDiv ℓ p (2 * (e * n)) := by
      rw [show 2 * (e * n) = e * (2 * n) by ring]
      exact hℓ
    refine ⟨2 * n, ℓ, by omega, hℓ, htr hℓ ?_ ?_, ?_, fun h => ?_⟩
    · exact Dvd.dvd.mul_right (hℓ'.dvd_pow_pow_add_one (by positivity)) _
    · exact hsmall hℓ (by omega) (Nat.gcd_pos_of_pos_left _ (by norm_num))
        (Nat.gcd_le_left _ (by norm_num))
    · change 2 * (n * (n - 1)) ≤ 2 * n * (2 * n - 1)
      have := Nat.mul_le_mul_left n (show n - 1 ≤ 2 * n - 1 by omega)
      nlinarith
    · exfalso
      change 2 * (n * (n - 1)) = 2 * n * (2 * n - 1) at h
      have : n * (n - 1) < n * (2 * n - 1) := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      nlinarith
  | G2 =>
    obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ e * 6 by omega)
    refine ⟨6, ℓ, by norm_num, hℓ, htr hℓ ?_ ?_, ?_, fun h => ?_⟩
    · exact Dvd.dvd.mul_right hℓ.dvd_pow_pow_sub_one _
    · change ¬ ℓ ∣ 1
      exact hsmall hℓ (by norm_num) one_pos (by norm_num)
    · change 2 * 6 ≤ 6 * (6 - 1)
      norm_num
    · change 2 * 6 = 6 * (6 - 1) at h
      norm_num at h
  | F4 =>
    obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ e * 12 by omega)
    refine ⟨12, ℓ, by norm_num, hℓ, htr hℓ ?_ ?_, ?_, fun h => ?_⟩
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
        hℓ.dvd_pow_pow_sub_one _) _) _
    · change ¬ ℓ ∣ 1
      exact hsmall hℓ (by norm_num) one_pos (by norm_num)
    · change 2 * 24 ≤ 12 * (12 - 1)
      norm_num
    · change 2 * 24 = 12 * (12 - 1) at h
      norm_num at h
  | E6 =>
    obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ e * 12 by omega)
    refine ⟨12, ℓ, by norm_num, hℓ, htr hℓ ?_ ?_, ?_, fun h => ?_⟩
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
        (Dvd.dvd.mul_right hℓ.dvd_pow_pow_sub_one _) _) _) _) _
    · change ¬ ℓ ∣ Nat.gcd 3 (p ^ e - 1)
      exact hsmall hℓ (by norm_num) (Nat.gcd_pos_of_pos_left _ (by norm_num))
        (le_trans (Nat.gcd_le_left _ (by norm_num)) (by norm_num))
    · change 2 * 36 ≤ 12 * (12 - 1)
      norm_num
    · change 2 * 36 = 12 * (12 - 1) at h
      norm_num at h
  | E7 =>
    obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ e * 18 by omega)
    refine ⟨18, ℓ, by norm_num, hℓ, htr hℓ ?_ ?_, ?_, fun h => ?_⟩
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
        (Dvd.dvd.mul_right (Dvd.dvd.mul_right hℓ.dvd_pow_pow_sub_one _) _) _) _) _) _
    · change ¬ ℓ ∣ Nat.gcd 2 (p ^ e - 1)
      exact hsmall hℓ (by norm_num) (Nat.gcd_pos_of_pos_left _ (by norm_num))
        (le_trans (Nat.gcd_le_left _ (by norm_num)) (by norm_num))
    · change 2 * 63 ≤ 18 * (18 - 1)
      norm_num
    · change 2 * 63 = 18 * (18 - 1) at h
      norm_num at h
  | E8 =>
    obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ e * 30 by omega)
    refine ⟨30, ℓ, by norm_num, hℓ, htr hℓ ?_ ?_, ?_, fun h => ?_⟩
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
        (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right hℓ.dvd_pow_pow_sub_one _)
          _) _) _) _) _) _
    · change ¬ ℓ ∣ 1
      exact hsmall hℓ (by norm_num) one_pos (by norm_num)
    · change 2 * 120 ≤ 30 * (30 - 1)
      norm_num
    · change 2 * 120 = 30 * (30 - 1) at h
      norm_num at h
  | twistedE6 =>
    obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ e * 12 by omega)
    refine ⟨12, ℓ, by norm_num, hℓ, htr hℓ ?_ ?_, ?_, fun h => ?_⟩
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
        (Dvd.dvd.mul_right hℓ.dvd_pow_pow_sub_one _) _) _) _) _
    · change ¬ ℓ ∣ Nat.gcd 3 (p ^ e + 1)
      exact hsmall hℓ (by norm_num) (Nat.gcd_pos_of_pos_left _ (by norm_num))
        (le_trans (Nat.gcd_le_left _ (by norm_num)) (by norm_num))
    · change 2 * 36 ≤ 12 * (12 - 1)
      norm_num
    · change 2 * 36 = 12 * (12 - 1) at h
      norm_num at h
  | trialityD4 =>
    obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ e * 6 by omega)
    refine ⟨6, ℓ, by norm_num, hℓ, htr hℓ ?_ ?_, ?_, fun h => ?_⟩
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hℓ.dvd_pow_pow_sub_one _) _
    · change ¬ ℓ ∣ 1
      exact hsmall hℓ (by norm_num) one_pos (by norm_num)
    · change 2 * 12 ≤ 6 * (6 - 1)
      norm_num
    · change 2 * 12 = 6 * (6 - 1) at h
      norm_num at h
  | twistedB2 => exact absurd hadm.2.2.2.1 hp2
  | twistedG2 =>
    obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ e * 6 by omega)
    have hℓ' : IsPrimDiv ℓ p (2 * (e * 3)) := by rw [show 2 * (e * 3) = e * 6 by ring]; exact hℓ
    refine ⟨6, ℓ, by norm_num, hℓ, htr hℓ ?_ ?_, ?_, fun h => ?_⟩
    · exact Dvd.dvd.mul_right (hℓ'.dvd_pow_pow_add_one (by positivity)) _
    · change ¬ ℓ ∣ 1
      exact hsmall hℓ (by norm_num) one_pos (by norm_num)
    · change 2 * 3 ≤ 6 * (6 - 1)
      norm_num
    · change 2 * 3 = 6 * (6 - 1) at h
      norm_num at h
  | twistedF4 => exact absurd hadm.2.2.2.1 hp2
  | Tits => exact absurd hadm.2.2.2.1 hp2

end CFSG.ComponentClassification.HarrisLit.T1.P58b.OLie
