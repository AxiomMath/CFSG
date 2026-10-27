module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrderArith
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithLieOddClassical

public section

namespace CFSG.SeitzReduction.CrossChar

open Finset CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof CFSG.SeitzReduction.RankOne.LieOdd

theorem pow_sub_one_lt_pow {q : ℕ} (hq : 1 ≤ q) (d : ℕ) : q ^ d - 1 < q ^ d := by
  have := Nat.one_le_pow d q hq
  omega

theorem prod_Icc_two_sub_one_lt {q : ℕ} (hq : 1 ≤ q) {n : ℕ} (hn : 2 ≤ n) :
    ∏ i ∈ Icc 2 n, (q ^ i - 1) < q ^ (n * (n - 1) / 2 + n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => simpa using pow_sub_one_lt_pow hq 2
  | succ m hm ih =>
    rw [Finset.prod_Icc_succ_top (by omega), tri_succ,
      show m * (m - 1) / 2 + m + (m + 1) - 1 = (m * (m - 1) / 2 + m - 1) + (m + 1) by omega,
      pow_add q (m * (m - 1) / 2 + m - 1) (m + 1)]
    exact Nat.mul_lt_mul'' ih (pow_sub_one_lt_pow hq (m + 1))

abbrev psuFactor (q i : ℕ) : ℕ := if Even i then q ^ i - 1 else q ^ i + 1

theorem pow_sub_one_mul_pow_succ_add_one_lt {q : ℕ} (hq : 2 ≤ q) (a : ℕ) :
    (q ^ a - 1) * (q ^ (a + 1) + 1) < q ^ (2 * a + 1) := by
  have h1 : 1 ≤ q ^ a := Nat.one_le_pow a q (by omega)
  have h2 : q ^ a < q ^ (a + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  have h3 : q ^ (2 * a + 1) = q ^ a * q ^ (a + 1) := by rw [← pow_add]; ring_nf
  rw [h3]
  zify [h1]
  nlinarith

theorem prod_psu_odd_mul_le {q : ℕ} (hq : 2 ≤ q) (k : ℕ) :
    (∏ i ∈ Icc 2 (2 * k + 1), psuFactor q i) * q ≤ q ^ ((2 * k + 1) * (k + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1 + 1) + 1 by ring, Finset.prod_Icc_succ_top (by omega),
      Finset.prod_Icc_succ_top (by omega)]
    have he : psuFactor q (2 * k + 1 + 1) = q ^ (2 * k + 2) - 1 := by
      simp only [psuFactor, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, even_two_mul, ite_true]
    have ho : psuFactor q (2 * k + 1 + 1 + 1) = q ^ (2 * k + 3) + 1 := by
      have : ¬ Even (2 * k + 1 + 1 + 1) := by
        rw [Nat.not_even_iff_odd]; exact ⟨k + 1, by ring⟩
      simp only [psuFactor, this, ite_false, show 2 * k + 1 + 1 + 1 = 2 * k + 3 by ring]
    rw [he, ho]
    have hp := pow_sub_one_mul_pow_succ_add_one_lt hq (2 * k + 2)
    calc (∏ i ∈ Icc 2 (2 * k + 1), psuFactor q i) * (q ^ (2 * k + 2) - 1) *
          (q ^ (2 * k + 3) + 1) * q
        = ((∏ i ∈ Icc 2 (2 * k + 1), psuFactor q i) * q) *
            ((q ^ (2 * k + 2) - 1) * (q ^ (2 * k + 2 + 1) + 1)) := by ring
      _ ≤ q ^ ((2 * k + 1) * (k + 1)) * q ^ (2 * (2 * k + 2) + 1) :=
          Nat.mul_le_mul ih hp.le
      _ = q ^ ((2 * (k + 1) + 1) * (k + 1 + 1)) := by rw [← pow_add]; ring_nf

theorem prod_psu_lt {q : ℕ} (hq : 2 ≤ q) {n : ℕ} (hn : 2 ≤ n) :
    ∏ i ∈ Icc 2 n, psuFactor q i < q ^ (n * (n - 1) / 2 + n - 1) := by
  have hq0 : 0 < q := by omega
  obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k + 2 ∨ n = 2 * k + 3 := by
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
    · exact ⟨k - 1, Or.inl (by omega)⟩
    · exact ⟨k - 1, Or.inr (by omega)⟩
  · rw [show 2 * k + 2 = 2 * k + 1 + 1 by ring, Finset.prod_Icc_succ_top (by omega)]
    have he : psuFactor q (2 * k + 1 + 1) = q ^ (2 * k + 2) - 1 := by
      simp only [psuFactor, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, even_two_mul, ite_true]
    rw [he]
    have h1 := prod_psu_odd_mul_le hq k
    have h2 := pow_sub_one_lt_pow (q := q) (by omega) (2 * k + 2)
    have hexp : (2 * k + 1 + 1) * (2 * k + 1 + 1 - 1) / 2 + (2 * k + 1 + 1) - 1 =
        (2 * k + 1) * (k + 2) := by
      rw [show (2 * k + 1 + 1) * (2 * k + 1 + 1 - 1) = 2 * ((k + 1) * (2 * k + 1)) by
        rw [show 2 * k + 1 + 1 - 1 = 2 * k + 1 by omega]; ring, Nat.mul_div_cancel_left _ two_pos]
      ring_nf; omega
    rw [hexp]
    refine Nat.lt_of_mul_lt_mul_right (a := q) ?_
    calc (∏ i ∈ Icc 2 (2 * k + 1), psuFactor q i) * (q ^ (2 * k + 2) - 1) * q
        = ((∏ i ∈ Icc 2 (2 * k + 1), psuFactor q i) * q) * (q ^ (2 * k + 2) - 1) := by ring
      _ < q ^ ((2 * k + 1) * (k + 1)) * q ^ (2 * k + 2) :=
          Nat.mul_lt_mul_of_le_of_lt h1 h2 (by positivity)
      _ = q ^ ((2 * k + 1) * (k + 2)) * q := by rw [← pow_succ, ← pow_add]; ring_nf
  · rw [show 2 * k + 3 = (2 * k + 1 + 1) + 1 by ring, Finset.prod_Icc_succ_top (by omega),
      Finset.prod_Icc_succ_top (by omega)]
    have he : psuFactor q (2 * k + 1 + 1) = q ^ (2 * k + 2) - 1 := by
      simp only [psuFactor, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, even_two_mul, ite_true]
    have ho : psuFactor q (2 * k + 1 + 1 + 1) = q ^ (2 * k + 3) + 1 := by
      have : ¬ Even (2 * k + 1 + 1 + 1) := by
        rw [Nat.not_even_iff_odd]; exact ⟨k + 1, by ring⟩
      simp only [psuFactor, this, ite_false, show 2 * k + 1 + 1 + 1 = 2 * k + 3 by ring]
    rw [he, ho]
    have h1 := prod_psu_odd_mul_le hq k
    have h2 := pow_sub_one_mul_pow_succ_add_one_lt hq (2 * k + 2)
    have hexp : (2 * k + 1 + 1 + 1) * (2 * k + 1 + 1 + 1 - 1) / 2 + (2 * k + 1 + 1 + 1) - 1 =
        2 * k * k + 7 * k + 5 := by
      rw [show (2 * k + 1 + 1 + 1) * (2 * k + 1 + 1 + 1 - 1) = 2 * ((2 * k + 3) * (k + 1)) by
        rw [show 2 * k + 1 + 1 + 1 - 1 = 2 * k + 2 by omega]; ring,
        Nat.mul_div_cancel_left _ two_pos]
      ring_nf; omega
    rw [hexp]
    refine Nat.lt_of_mul_lt_mul_right (a := q) ?_
    calc (∏ i ∈ Icc 2 (2 * k + 1), psuFactor q i) * (q ^ (2 * k + 2) - 1) *
          (q ^ (2 * k + 3) + 1) * q
        = ((∏ i ∈ Icc 2 (2 * k + 1), psuFactor q i) * q) *
            ((q ^ (2 * k + 2) - 1) * (q ^ (2 * k + 2 + 1) + 1)) := by ring
      _ < q ^ ((2 * k + 1) * (k + 1)) * q ^ (2 * (2 * k + 2) + 1) :=
          Nat.mul_lt_mul_of_le_of_lt h1 h2 (by positivity)
      _ = q ^ (2 * k * k + 7 * k + 5) * q := by rw [← pow_succ, ← pow_add]; ring_nf

theorem prod_Icc_one_sub_one_lt {q : ℕ} (hq : 1 ≤ q) {n : ℕ} (hn : 1 ≤ n) :
    ∏ i ∈ Icc 1 n, (q ^ (2 * i) - 1) < q ^ (n * (n + 1)) := by
  induction n, hn using Nat.le_induction with
  | base => simpa using pow_sub_one_lt_pow hq 2
  | succ m hm ih =>
    rw [Finset.prod_Icc_succ_top (by omega),
      show (m + 1) * (m + 1 + 1) = m * (m + 1) + 2 * (m + 1) by ring,
      pow_add q (m * (m + 1)) (2 * (m + 1))]
    exact Nat.mul_lt_mul'' ih (pow_sub_one_lt_pow hq (2 * (m + 1)))

theorem four_mul_lt_of_lt_pow {q C E N : ℕ} (hq : 2 ≤ q) (hC : C < q ^ E) (hE : E + 2 ≤ 2 * N) :
    4 * C < q ^ (2 * N) := by
  calc 4 * C < 4 * q ^ E := by omega
    _ ≤ q ^ 2 * q ^ E := Nat.mul_le_mul_right _ (by nlinarith)
    _ = q ^ (E + 2) := by rw [← pow_add]; ring_nf
    _ ≤ q ^ (2 * N) := Nat.pow_le_pow_right (by omega) hE

theorem lt_of_lt_pow {q C E N : ℕ} (hq : 1 ≤ q) (hC : C < q ^ E) (hE : E ≤ 2 * N) :
    C < q ^ (2 * N) :=
  hC.trans_le (Nat.pow_le_pow_right hq hE)

theorem two_mul_tri (n : ℕ) : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
  Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)

theorem pow_add_one_le_pow_succ {q : ℕ} (hq : 2 ≤ q) (d : ℕ) : q ^ d + 1 ≤ q ^ (d + 1) := by
  rw [pow_succ]
  have := Nat.one_le_pow d q (by omega)
  nlinarith

theorem exc_bound {q C S N : ℕ} (hq : 2 ≤ q) (hC : C ≤ q ^ S) (hS : S + 3 ≤ 2 * N)
    {P Q : Prop} : C < q ^ (2 * N) ∧ (P → Q → 4 * C < q ^ (2 * N)) := by
  have hC' : C < q ^ (S + 1) := hC.trans_lt (Nat.pow_lt_pow_right (by omega) (by omega))
  exact ⟨lt_of_lt_pow (by omega) hC' (by omega),
    fun _ _ => four_mul_lt_of_lt_pow hq hC' (by omega)⟩

theorem cofactor_lt_two {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f) :
    lieOrderCofactor t n (2 ^ f) < (2 ^ f) ^ (2 * lieSylowExponent t n) ∧
      (¬ (t = .PSL ∧ n = 2) → ¬ (t = .PSL ∧ n = 3 ∧ f = 1) →
        4 * lieOrderCofactor t n (2 ^ f) < (2 ^ f) ^ (2 * lieSylowExponent t n)) := by
  have hf : 1 ≤ f := hadm.2.1
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hq1 : 1 ≤ 2 ^ f := by omega
  set q := 2 ^ f with hqdef
  cases t
  case PSL =>
    obtain ⟨-, -, hn, -, -⟩ := hadm
    have hC := prod_Icc_two_sub_one_lt hq1 hn
    have h2N := two_mul_tri n
    refine ⟨lt_of_lt_pow hq1 hC (by
      show n * (n - 1) / 2 + n - 1 ≤ 2 * (n * (n - 1) / 2)
      have : 2 * (n - 1) ≤ n * (n - 1) := Nat.mul_le_mul_right _ (by omega)
      omega), fun h2 h3 => ?_⟩
    rcases (by omega : n = 2 ∨ n = 3 ∨ 4 ≤ n) with rfl | rfl | h4
    · exact absurd ⟨rfl, rfl⟩ h2
    · have hf2 : 2 ≤ f := by
        by_contra hlt
        exact h3 ⟨rfl, rfl, by omega⟩
      have hq4 : 4 ≤ q := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      have hC3 : lieOrderCofactor .PSL 3 q < q ^ 5 := hC
      show 4 * lieOrderCofactor .PSL 3 q < q ^ 6
      calc 4 * lieOrderCofactor .PSL 3 q < 4 * q ^ 5 := by omega
        _ ≤ q * q ^ 5 := Nat.mul_le_mul_right _ hq4
        _ = q ^ 6 := by ring
    · refine four_mul_lt_of_lt_pow hq hC ?_
      show n * (n - 1) / 2 + n - 1 + 2 ≤ 2 * (n * (n - 1) / 2)
      rw [h2N]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      simp only [show k + 4 - 1 = k + 3 by omega] at h2N ⊢
      have : (k + 4) * (k + 3) / 2 ≥ k + 6 := by
        have : 2 * (k + 6) ≤ (k + 4) * (k + 3) := by nlinarith
        omega
      omega
  case PSU =>
    obtain ⟨-, -, hn, hn3⟩ := hadm
    have hC := prod_psu_lt hq (by omega : 2 ≤ n)
    have h2N := two_mul_tri n
    refine ⟨lt_of_lt_pow hq1 hC (by
      show n * (n - 1) / 2 + n - 1 ≤ 2 * (n * (n - 1) / 2)
      have : 2 * (n - 1) ≤ n * (n - 1) := Nat.mul_le_mul_right _ (by omega)
      omega), fun _ _ => ?_⟩
    rcases (by omega : n = 3 ∨ 4 ≤ n) with rfl | h4
    · have hf2 : 2 ≤ f := by
        by_contra hlt
        obtain rfl : f = 1 := by omega
        exact hn3 rfl
      have hq4 : 4 ≤ q := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      have hC3 : lieOrderCofactor .PSU 3 q < q ^ 5 := hC
      show 4 * lieOrderCofactor .PSU 3 q < q ^ 6
      calc 4 * lieOrderCofactor .PSU 3 q < 4 * q ^ 5 := by omega
        _ ≤ q * q ^ 5 := Nat.mul_le_mul_right _ hq4
        _ = q ^ 6 := by ring
    · refine four_mul_lt_of_lt_pow hq hC ?_
      show n * (n - 1) / 2 + n - 1 + 2 ≤ 2 * (n * (n - 1) / 2)
      rw [h2N]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      simp only [show k + 4 - 1 = k + 3 by omega] at h2N ⊢
      have : (k + 4) * (k + 3) / 2 ≥ k + 6 := by
        have : 2 * (k + 6) ≤ (k + 4) * (k + 3) := by nlinarith
        omega
      omega
  case PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    have hC := prod_Icc_one_sub_one_lt hq1 (by omega : 1 ≤ n)
    have hE : n * (n + 1) + 2 ≤ 2 * lieSylowExponent .PSp n := by
      simp only [lieSylowExponent]; nlinarith
    exact ⟨lt_of_lt_pow hq1 hC (by omega), fun _ _ => four_mul_lt_of_lt_pow hq hC hE⟩
  case POmegaOdd => exact absurd rfl hadm.2.2.2
  case POmegaPlus =>
    obtain ⟨-, -, hn⟩ := hadm
    have hP := prod_Icc_one_sub_one_lt hq1 (by omega : 1 ≤ n - 1)
    have hC : lieOrderCofactor .POmegaPlus n q < q ^ (n + (n - 1) * (n - 1 + 1)) := by
      rw [pow_add]
      exact Nat.mul_lt_mul'' (pow_sub_one_lt_pow hq1 n) hP
    have hE : n + (n - 1) * (n - 1 + 1) + 2 ≤ 2 * lieSylowExponent .POmegaPlus n := by
      simp only [lieSylowExponent]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      simp only [show k + 4 - 1 = k + 3 by omega]; nlinarith
    exact ⟨lt_of_lt_pow hq1 hC (by omega), fun _ _ => four_mul_lt_of_lt_pow hq hC hE⟩
  case POmegaMinus =>
    obtain ⟨-, -, hn⟩ := hadm
    have hP := prod_Icc_one_sub_one_lt hq1 (by omega : 1 ≤ n - 1)
    have hX : q ^ n + 1 ≤ q ^ (n + 1) := by
      rw [pow_succ]
      have := Nat.one_le_pow n q hq1
      nlinarith
    have hC : lieOrderCofactor .POmegaMinus n q < q ^ (n + 1 + (n - 1) * (n - 1 + 1)) := by
      rw [pow_add]
      exact Nat.mul_lt_mul_of_le_of_lt hX hP (by positivity)
    have hE : n + 1 + (n - 1) * (n - 1 + 1) + 2 ≤ 2 * lieSylowExponent .POmegaMinus n := by
      simp only [lieSylowExponent]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      simp only [show k + 4 - 1 = k + 3 by omega]; nlinarith
    exact ⟨lt_of_lt_pow hq1 hC (by omega), fun _ _ => four_mul_lt_of_lt_pow hq hC hE⟩
  case G2 =>
    have hC : lieOrderCofactor .G2 n q ≤ q ^ 8 := by
      show (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 8
      calc (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 6 * q ^ 2 := by gcongr <;> exact Nat.sub_le _ _
        _ = q ^ 8 := by ring
    exact exc_bound hq hC (by simp [lieSylowExponent])
  case F4 =>
    have hC : lieOrderCofactor .F4 n q ≤ q ^ 28 := by
      show (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 28
      calc (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
          ≤ q ^ 12 * q ^ 8 * q ^ 6 * q ^ 2 := by gcongr <;> exact Nat.sub_le _ _
        _ = q ^ 28 := by ring
    exact exc_bound hq hC (by simp [lieSylowExponent])
  case E6 =>
    have hC : lieOrderCofactor .E6 n q ≤ q ^ 42 := by
      show (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1) ≤
        q ^ 42
      calc (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1)
          ≤ q ^ 12 * q ^ 9 * q ^ 8 * q ^ 6 * q ^ 5 * q ^ 2 := by
            gcongr <;> exact Nat.sub_le _ _
        _ = q ^ 42 := by ring
    exact exc_bound hq hC (by simp [lieSylowExponent])
  case E7 =>
    have hC : lieOrderCofactor .E7 n q ≤ q ^ 70 := by
      show (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
        (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 70
      calc (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
            (q ^ 6 - 1) * (q ^ 2 - 1)
          ≤ q ^ 18 * q ^ 14 * q ^ 12 * q ^ 10 * q ^ 8 * q ^ 6 * q ^ 2 := by
            gcongr <;> exact Nat.sub_le _ _
        _ = q ^ 70 := by ring
    exact exc_bound hq hC (by simp [lieSylowExponent])
  case E8 =>
    have hC : lieOrderCofactor .E8 n q ≤ q ^ 128 := by
      show (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) *
        (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1) ≤ q ^ 128
      calc (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) *
            (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)
          ≤ q ^ 30 * q ^ 24 * q ^ 20 * q ^ 18 * q ^ 14 * q ^ 12 * q ^ 8 * q ^ 2 := by
            gcongr <;> exact Nat.sub_le _ _
        _ = q ^ 128 := by ring
    exact exc_bound hq hC (by simp [lieSylowExponent])
  case twistedE6 =>
    have hC : lieOrderCofactor .twistedE6 n q ≤ q ^ 44 := by
      show (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1) ≤
        q ^ 44
      calc (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1)
          ≤ q ^ 12 * q ^ 10 * q ^ 8 * q ^ 6 * q ^ 6 * q ^ 2 := by
            gcongr
            · exact Nat.sub_le _ _
            · exact pow_add_one_le_pow_succ hq 9
            · exact Nat.sub_le _ _
            · exact Nat.sub_le _ _
            · exact pow_add_one_le_pow_succ hq 5
            · exact Nat.sub_le _ _
        _ = q ^ 44 := by ring
    exact exc_bound hq hC (by simp [lieSylowExponent])
  case trialityD4 =>
    have hC : lieOrderCofactor .trialityD4 n q ≤ q ^ 17 := by
      show (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 17
      have h8 : q ^ 8 + q ^ 4 + 1 ≤ q ^ 9 := by
        have h4 : q ^ 4 + 1 ≤ q ^ 8 := by
          have : q ^ 4 + 1 ≤ q ^ 5 := pow_add_one_le_pow_succ hq 4
          exact this.trans (Nat.pow_le_pow_right (by omega) (by norm_num))
        have : q ^ 8 + 1 ≤ q ^ 9 := pow_add_one_le_pow_succ hq 8
        nlinarith [Nat.one_le_pow 8 q (by omega)]
      calc (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 9 * q ^ 6 * q ^ 2 := by
            gcongr <;> exact Nat.sub_le _ _
        _ = q ^ 17 := by ring
    exact exc_bound hq hC (by simp [lieSylowExponent])
  case twistedB2 =>
    obtain ⟨-, -, -, -, -, hf3⟩ := hadm
    have hq8 : 8 ≤ q := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
    have hC : lieOrderCofactor .twistedB2 n q < q ^ 3 := by
      show (q ^ 2 + 1) * (q - 1) < q ^ 3
      have h1 : q - 1 + 1 = q := by omega
      have h2 : (q ^ 2 + 1) * (q - 1) + q ^ 2 = q ^ 3 + (q - 1) := by
        rw [← h1]; simp only [Nat.add_sub_cancel]; ring
      have h3 : q - 1 < q ^ 2 := by nlinarith
      omega
    refine ⟨lt_of_lt_pow hq1 hC (by simp [lieSylowExponent]), fun _ _ => ?_⟩
    show 4 * lieOrderCofactor .twistedB2 n q < q ^ (2 * 2)
    calc 4 * lieOrderCofactor .twistedB2 n q < 4 * q ^ 3 := by omega
      _ ≤ q * q ^ 3 := Nat.mul_le_mul_right _ (by omega)
      _ = q ^ (2 * 2) := by ring
  case twistedF4 =>
    have hC : lieOrderCofactor .twistedF4 n q ≤ q ^ 16 := by
      show (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) ≤ q ^ 16
      calc (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) ≤ q ^ 7 * q ^ 4 * q ^ 4 * q := by
            gcongr
            · exact pow_add_one_le_pow_succ hq 6
            · exact Nat.sub_le _ _
            · exact pow_add_one_le_pow_succ hq 3
            · exact Nat.sub_le _ _
        _ = q ^ 16 := by ring
    exact exc_bound hq hC (by simp [lieSylowExponent])
  case twistedG2 => exact absurd hadm.2.2.2.1 (by norm_num)
  case Tits =>
    obtain ⟨-, -, -, -, rfl⟩ := hadm
    have h1 : lieOrderCofactor .Tits n (2 ^ 1) = 8775 := rfl
    have h2 : lieSylowExponent .Tits n = 11 := rfl
    rw [h1, h2]
    exact ⟨by norm_num, fun _ _ => by norm_num⟩

theorem ordProj_two_eq_of_two {t : StatedLieTag} {n f M : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f)) :
    ordProj[2] M = 2 ^ (lieSylowExponent t n * f) := by
  rw [lieOrderNumerator_eq hadm, ← pow_mul, mul_comm f] at hM
  have hC : Odd (lieOrderCofactor t n (2 ^ f)) :=
    Nat.coprime_two_right.mp (lieOrderCofactor_coprime hadm)
  have hD : Odd (lieOrderDivisor t n (2 ^ f)) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (not_dvd_lieOrderDivisor hadm))
  have hM0 : M ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hM
    exact (mul_ne_zero (pow_ne_zero _ two_ne_zero) (lieOrderCofactor_ne_zero hadm)) hM.symm
  have h : ordProj[2] (M * lieOrderDivisor t n (2 ^ f)) =
      ordProj[2] (2 ^ (lieSylowExponent t n * f) * lieOrderCofactor t n (2 ^ f)) := by rw [hM]
  rwa [ordProj_two_mul_odd hM0 hD, ordProj_two_pow_mul_odd hC] at h

theorem lt_cube_of_two {t : StatedLieTag} {n f M : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f)) :
    M < ordProj[2] M ^ 3 ∧ (¬ (t = .PSL ∧ n = 2) → ¬ (t = .PSL ∧ n = 3 ∧ f = 1) →
      4 * M < ordProj[2] M ^ 3) := by
  have hT : ordProj[2] M = (2 ^ f) ^ lieSylowExponent t n := by
    rw [ordProj_two_eq_of_two hadm hM, ← pow_mul, mul_comm]
  have hD : 1 ≤ lieOrderDivisor t n (2 ^ f) :=
    Nat.one_le_iff_ne_zero.mpr (lieOrderDivisor_ne_zero hadm)
  rw [lieOrderNumerator_eq hadm] at hM
  have hle : M ≤ (2 ^ f) ^ lieSylowExponent t n * lieOrderCofactor t n (2 ^ f) :=
    hM ▸ Nat.le_mul_of_pos_right M hD
  have hP : 0 < (2 ^ f) ^ lieSylowExponent t n := by positivity
  have hcube : ((2 ^ f) ^ lieSylowExponent t n) ^ 3 =
      (2 ^ f) ^ lieSylowExponent t n * (2 ^ f) ^ (2 * lieSylowExponent t n) := by
    rw [← pow_mul, ← pow_add]; ring_nf
  obtain ⟨h1, h2⟩ := cofactor_lt_two hadm
  rw [hT, hcube]
  refine ⟨hle.trans_lt (Nat.mul_lt_mul_of_pos_left h1 hP), fun hn2 hn3 => ?_⟩
  calc 4 * M ≤ 4 * ((2 ^ f) ^ lieSylowExponent t n * lieOrderCofactor t n (2 ^ f)) := by omega
    _ = (2 ^ f) ^ lieSylowExponent t n * (4 * lieOrderCofactor t n (2 ^ f)) := by ring
    _ < (2 ^ f) ^ lieSylowExponent t n * (2 ^ f) ^ (2 * lieSylowExponent t n) :=
        Nat.mul_lt_mul_of_pos_left (h2 hn2 hn3) hP

theorem eq_of_sylow_mul_eq_five {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (h : lieSylowExponent t n * f = 5) : t = .PSL ∧ n = 2 ∧ f = 5 := by
  have hf : 1 ≤ f := hadm.2.1
  cases t
  case PSL =>
    obtain ⟨-, -, hn, -, -⟩ := hadm
    simp only [lieSylowExponent] at h
    have hN : n * (n - 1) / 2 ≤ 5 := by
      have := Nat.le_mul_of_pos_right (n * (n - 1) / 2) (show 0 < f by omega); omega
    have hn5 : n ≤ 4 := by
      by_contra hlt
      have : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    interval_cases n
    · exact ⟨rfl, rfl, by simpa using h⟩
    · norm_num at h; omega
    · norm_num at h; omega
  case PSU =>
    obtain ⟨-, -, hn, -⟩ := hadm
    simp only [lieSylowExponent] at h
    have hN : n * (n - 1) / 2 ≤ 5 := by
      have := Nat.le_mul_of_pos_right (n * (n - 1) / 2) (show 0 < f by omega); omega
    have hn5 : n ≤ 4 := by
      by_contra hlt
      have : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    interval_cases n <;> norm_num at h <;> omega
  case PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    simp only [lieSylowExponent] at h
    have : 4 ≤ n ^ 2 := by nlinarith
    have : 4 * f ≤ n ^ 2 * f := Nat.mul_le_mul_right _ this
    rcases (by omega : n ^ 2 * f = 5 ∧ f = 1) with ⟨h1, rfl⟩
    have h5 : n ^ 2 = 5 := by omega
    have : n ≤ 2 := by nlinarith
    obtain rfl : n = 2 := by omega
    norm_num at h5
  case POmegaOdd => exact absurd rfl hadm.2.2.2
  case POmegaPlus =>
    obtain ⟨-, -, hn⟩ := hadm
    simp only [lieSylowExponent] at h
    have : 12 ≤ n * (n - 1) := Nat.mul_le_mul (by omega : 4 ≤ n) (by omega : 3 ≤ n - 1)
    nlinarith
  case POmegaMinus =>
    obtain ⟨-, -, hn⟩ := hadm
    simp only [lieSylowExponent] at h
    have : 12 ≤ n * (n - 1) := Nat.mul_le_mul (by omega : 4 ≤ n) (by omega : 3 ≤ n - 1)
    nlinarith
  case twistedG2 => exact absurd hadm.2.2.2.1 (by norm_num)
  all_goals simp only [lieSylowExponent] at h; omega

theorem eq_of_sylow_mul_eq_six {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (h : lieSylowExponent t n * f = 6) :
    (t = .PSL ∧ n = 2 ∧ f = 6) ∨ (t = .PSL ∧ n = 3 ∧ f = 2) ∨ (t = .PSL ∧ n = 4 ∧ f = 1) ∨
      (t = .PSU ∧ n = 3 ∧ f = 2) ∨ (t = .PSU ∧ n = 4 ∧ f = 1) ∨
      (t = .twistedB2 ∧ n = 0 ∧ f = 3) := by
  have hf : 1 ≤ f := hadm.2.1
  cases t
  case PSL =>
    obtain ⟨-, -, hn, -, -⟩ := hadm
    simp only [lieSylowExponent] at h
    have hN : n * (n - 1) / 2 ≤ 6 := by
      have := Nat.le_mul_of_pos_right (n * (n - 1) / 2) (show 0 < f by omega); omega
    have hn5 : n ≤ 4 := by
      by_contra hlt
      have : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    interval_cases n
    · exact Or.inl ⟨rfl, rfl, by simpa using h⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl, by norm_num at h; omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by norm_num at h; omega⟩))
  case PSU =>
    obtain ⟨-, -, hn, hn3⟩ := hadm
    simp only [lieSylowExponent] at h
    have hN : n * (n - 1) / 2 ≤ 6 := by
      have := Nat.le_mul_of_pos_right (n * (n - 1) / 2) (show 0 < f by omega); omega
    have hn5 : n ≤ 4 := by
      by_contra hlt
      have : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    interval_cases n
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by norm_num at h; omega⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by norm_num at h; omega⟩))))
  case PSp =>
    obtain ⟨-, -, hn, hn2⟩ := hadm
    simp only [lieSylowExponent] at h
    have h4 : 4 ≤ n ^ 2 := by nlinarith
    have : 4 * f ≤ n ^ 2 * f := Nat.mul_le_mul_right _ h4
    obtain rfl : f = 1 := by omega
    have h6 : n ^ 2 = 6 := by omega
    have : n ≤ 2 := by nlinarith
    obtain rfl : n = 2 := by omega
    norm_num at h6
  case POmegaOdd => exact absurd rfl hadm.2.2.2
  case POmegaPlus =>
    obtain ⟨-, -, hn⟩ := hadm
    simp only [lieSylowExponent] at h
    have : 12 ≤ n * (n - 1) := Nat.mul_le_mul (by omega : 4 ≤ n) (by omega : 3 ≤ n - 1)
    nlinarith
  case POmegaMinus =>
    obtain ⟨-, -, hn⟩ := hadm
    simp only [lieSylowExponent] at h
    have : 12 ≤ n * (n - 1) := Nat.mul_le_mul (by omega : 4 ≤ n) (by omega : 3 ≤ n - 1)
    nlinarith
  case G2 =>
    obtain ⟨-, -, -, hq⟩ := hadm
    simp only [lieSylowExponent] at h
    obtain rfl : f = 1 := by omega
    norm_num at hq
  case twistedB2 =>
    simp only [lieSylowExponent] at h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hadm.2.2.1, by omega⟩))))
  case twistedG2 => exact absurd hadm.2.2.2.1 (by norm_num)
  all_goals simp only [lieSylowExponent] at h; omega

end CFSG.SeitzReduction.CrossChar
