module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithLieOddClassical
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithLieOddExceptional
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrderArith

public section

namespace CFSG.SeitzReduction.CrossChar

open Finset CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof CFSG.SeitzReduction.RankOne.LieOdd

theorem mul_succ_pow_le_of_le {q₀ q K a b c : ℕ} (hq₀ : 2 ≤ q₀) (hq : q₀ ≤ q)
    (habc : a ≤ b + c) (h₀ : K * (q₀ + 1) ^ a ≤ q₀ ^ b * (q₀ - 1) ^ c) :
    K * (q + 1) ^ a ≤ q ^ b * (q - 1) ^ c := by
  obtain ⟨a₁, a₂, rfl, h1, h2⟩ : ∃ a₁ a₂, a = a₁ + a₂ ∧ a₁ ≤ b ∧ a₂ ≤ c :=
    ⟨min a b, a - min a b, by omega, min_le_right _ _, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = a₁ + b' := ⟨b - a₁, by omega⟩
  obtain ⟨c', rfl⟩ : ∃ c', c = a₂ + c' := ⟨c - a₂, by omega⟩
  obtain ⟨x, rfl⟩ : ∃ x, q₀ = x + 2 := ⟨q₀ - 2, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, q = y + 2 := ⟨q - 2, by omega⟩
  simp only [show x + 2 - 1 = x + 1 by omega, show y + 2 - 1 = y + 1 by omega] at h₀ ⊢
  have e1 : (x + 2) * (y + 2 + 1) ≤ (x + 2 + 1) * (y + 2) := by nlinarith
  have e2 : (x + 1) * (y + 2 + 1) ≤ (x + 2 + 1) * (y + 1) := by nlinarith
  have hpos : 0 < (x + 2) ^ a₁ * (x + 1) ^ a₂ := by positivity
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc (x + 2) ^ a₁ * (x + 1) ^ a₂ * (K * (y + 2 + 1) ^ (a₁ + a₂))
      = K * (((x + 2) * (y + 2 + 1)) ^ a₁ * ((x + 1) * (y + 2 + 1)) ^ a₂) := by
        rw [mul_pow, mul_pow, pow_add]; ring
    _ ≤ K * (((x + 2 + 1) * (y + 2)) ^ a₁ * ((x + 2 + 1) * (y + 1)) ^ a₂) := by gcongr
    _ = K * (x + 2 + 1) ^ (a₁ + a₂) * ((y + 2) ^ a₁ * (y + 1) ^ a₂) := by
        rw [mul_pow, mul_pow, pow_add]; ring
    _ ≤ (x + 2) ^ (a₁ + b') * (x + 1) ^ (a₂ + c') * ((y + 2) ^ a₁ * (y + 1) ^ a₂) := by gcongr
    _ = (x + 2) ^ a₁ * (x + 1) ^ a₂ * ((x + 2) ^ b' * (x + 1) ^ c' *
          ((y + 2) ^ a₁ * (y + 1) ^ a₂)) := by ring
    _ ≤ (x + 2) ^ a₁ * (x + 1) ^ a₂ * ((y + 2) ^ b' * (y + 1) ^ c' *
          ((y + 2) ^ a₁ * (y + 1) ^ a₂)) := by gcongr; omega
    _ = (x + 2) ^ a₁ * (x + 1) ^ a₂ * ((y + 2) ^ (a₁ + b') * (y + 1) ^ (a₂ + c')) := by ring

theorem ordProj_cube_le_of_twoPartBound {q N C L B G D M : ℕ} (hqodd : Odd q)
    (hb : TwoPartBound C L B) (hcrit : B ^ 3 * G ≤ q ^ N * L) (hM : M * D = q ^ N * C)
    (hD : 0 < D) (hDG : D ≤ G) : ordProj[2] M ^ 3 ≤ M := by
  have hqN : q ^ N ≠ 0 := pow_ne_zero _ hqodd.pos.ne'
  have hM0 : M ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hM
    exact mul_ne_zero hqN hb.ne_zero hM.symm
  have h1 : ordProj[2] M ≤ B := by
    have hmul : ordProj[2] (M * D) = ordProj[2] M * ordProj[2] D := Nat.ordProj_mul 2 hM0 hD.ne'
    have h2 : ordProj[2] (q ^ N * C) = ordProj[2] C := by
      rw [Nat.ordProj_mul 2 hqN hb.ne_zero, ordProj_two_of_odd hqodd.pow, one_mul]
    have h3 : 1 ≤ ordProj[2] D := Nat.one_le_pow _ _ two_pos
    calc ordProj[2] M ≤ ordProj[2] M * ordProj[2] D := Nat.le_mul_of_pos_right _ h3
      _ = ordProj[2] C := by rw [← hmul, hM, h2]
      _ ≤ B := hb.ordProj_le
  have h4 : B ^ 3 * G ≤ M * G :=
    calc B ^ 3 * G ≤ q ^ N * L := hcrit
      _ ≤ q ^ N * C := Nat.mul_le_mul_left _ hb.le
      _ = M * D := hM.symm
      _ ≤ M * G := Nat.mul_le_mul_left _ hDG
  calc ordProj[2] M ^ 3 ≤ B ^ 3 := Nat.pow_le_pow_left h1 3
    _ ≤ M := Nat.le_of_mul_le_mul_right h4 (lt_of_lt_of_le hD hDG)

theorem ordProj_cube_le_of_eq {M D k r : ℕ} (hM : M * D = D * (2 ^ k * r)) (hD : 0 < D)
    (hr : Odd r) (hle : (2 ^ k) ^ 3 ≤ 2 ^ k * r) : ordProj[2] M ^ 3 ≤ M := by
  have hM' : M = 2 ^ k * r := by
    rw [mul_comm] at hM
    exact Nat.eq_of_mul_eq_mul_left hD hM
  rw [hM', ordProj_two_pow_mul_odd hr]
  exact hle

theorem eq_of_mul_eq_mul {M D V : ℕ} (hM : M * D = D * V) (hD : 0 < D) : M = V := by
  rw [mul_comm] at hM
  exact Nat.eq_of_mul_eq_mul_left hD hM

theorem aux_crossA (k : ℕ) : 2 ^ (8 * (k + 5)) * (k + 6) ≤ 3 ^ ((k + 6) * (k + 5)) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have e1 : 512 ≤ 3 ^ (2 * (k + 6)) :=
      calc 512 ≤ 3 ^ 12 := by norm_num
        _ ≤ 3 ^ (2 * (k + 6)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 ^ (8 * (k + 1 + 5)) * (k + 1 + 6) = 2 ^ 8 * (2 ^ (8 * (k + 5)) * (k + 7)) := by ring
      _ ≤ 2 ^ 8 * (2 ^ (8 * (k + 5)) * (2 * (k + 6))) := by gcongr; omega
      _ = 512 * (2 ^ (8 * (k + 5)) * (k + 6)) := by ring
      _ ≤ 3 ^ (2 * (k + 6)) * 3 ^ ((k + 6) * (k + 5)) := Nat.mul_le_mul e1 ih
      _ = 3 ^ ((k + 1 + 6) * (k + 1 + 5)) := by rw [← pow_add]; ring_nf

theorem aux_crossB (k : ℕ) : 2 ^ (11 * k + 42) ≤ 3 ^ (2 * (k + 4) ^ 2) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have e1 : 2 ^ 11 ≤ 3 ^ (4 * k + 18) :=
      calc 2 ^ 11 ≤ 3 ^ 18 := by norm_num
        _ ≤ 3 ^ (4 * k + 18) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 ^ (11 * (k + 1) + 42) = 2 ^ 11 * 2 ^ (11 * k + 42) := by ring
      _ ≤ 3 ^ (4 * k + 18) * 3 ^ (2 * (k + 4) ^ 2) := Nat.mul_le_mul e1 ih
      _ = 3 ^ (2 * (k + 1 + 4) ^ 2) := by rw [← pow_add]; ring_nf

theorem aux_crossC (k : ℕ) : 2 ^ (11 * k + 51) ≤ 3 ^ (2 * ((k + 5) * (k + 4))) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have e1 : 2 ^ 11 ≤ 3 ^ (4 * k + 20) :=
      calc 2 ^ 11 ≤ 3 ^ 20 := by norm_num
        _ ≤ 3 ^ (4 * k + 20) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 ^ (11 * (k + 1) + 51) = 2 ^ 11 * 2 ^ (11 * k + 51) := by ring
      _ ≤ 3 ^ (4 * k + 20) * 3 ^ (2 * ((k + 5) * (k + 4))) := Nat.mul_le_mul e1 ih
      _ = 3 ^ (2 * ((k + 1 + 5) * (k + 1 + 4))) := by rw [← pow_add]; ring_nf

theorem ordProj_two_factorial_three : ordProj[2] (Nat.factorial 3) = 2 ^ 1 := by
  rw [show Nat.factorial 3 = 2 ^ 1 * 3 by decide]
  exact ordProj_two_pow_mul_odd (by decide)

theorem ordProj_two_factorial_four : ordProj[2] (Nat.factorial 4) = 2 ^ 3 := by
  rw [show Nat.factorial 4 = 2 ^ 3 * 3 by decide]
  exact ordProj_two_pow_mul_odd (by decide)

theorem ordProj_two_factorial_five : ordProj[2] (Nat.factorial 5) = 2 ^ 3 := by
  rw [show Nat.factorial 5 = 2 ^ 3 * 15 by decide]
  exact ordProj_two_pow_mul_odd (by decide)

theorem pow_tri_mul_pow_tri (q m : ℕ) :
    q ^ (m * (m - 1) / 2) * q ^ (m * (m - 1) / 2) = q ^ (m * (m - 1)) := by
  rw [← pow_add, ← two_mul, Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self m)]

theorem critA {m q : ℕ} (hm : 3 ≤ m) (hq : 3 ≤ q) (h3 : m = 3 → 9 ≤ q) (h4 : m = 4 → 7 ≤ q) :
    ((q + 1) ^ (m - 1) * ordProj[2] m.factorial) ^ 3 * m ≤
      q ^ (m * (m - 1) / 2) * (q ^ (m * (m - 1) / 2) * (q - 1) ^ (m - 1)) := by
  rw [← mul_assoc, pow_tri_mul_pow_tri]
  rcases (by omega : m = 3 ∨ m = 4 ∨ m = 5 ∨ 6 ≤ m) with rfl | rfl | rfl | h6
  · rw [ordProj_two_factorial_three]
    calc ((q + 1) ^ (3 - 1) * 2 ^ 1) ^ 3 * 3 = 24 * (q + 1) ^ 6 := by norm_num; ring
      _ ≤ q ^ 6 * (q - 1) ^ 2 :=
        mul_succ_pow_le_of_le (q₀ := 9) (by norm_num) (h3 rfl) (by norm_num) (by norm_num)
      _ = q ^ (3 * (3 - 1)) * (q - 1) ^ (3 - 1) := by norm_num
  · rw [ordProj_two_factorial_four]
    calc ((q + 1) ^ (4 - 1) * 2 ^ 3) ^ 3 * 4 = 2048 * (q + 1) ^ 9 := by norm_num; ring
      _ ≤ q ^ 12 * (q - 1) ^ 3 :=
        mul_succ_pow_le_of_le (q₀ := 7) (by norm_num) (h4 rfl) (by norm_num) (by norm_num)
      _ = q ^ (4 * (4 - 1)) * (q - 1) ^ (4 - 1) := by norm_num
  · rw [ordProj_two_factorial_five]
    calc ((q + 1) ^ (5 - 1) * 2 ^ 3) ^ 3 * 5 = 2560 * (q + 1) ^ 12 := by norm_num; ring
      _ ≤ q ^ 20 * (q - 1) ^ 4 :=
        mul_succ_pow_le_of_le (q₀ := 3) (by norm_num) hq (by norm_num) (by norm_num)
      _ = q ^ (5 * (5 - 1)) * (q - 1) ^ (5 - 1) := by norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
    have hW := ordProj_two_factorial_le (m := k + 6) (by omega)
    simp only [show k + 6 - 1 = k + 5 by omega] at hW ⊢
    have hbase : 8 ^ (k + 5) * (k + 6) * (3 + 1) ^ (3 * (k + 5)) ≤
        3 ^ ((k + 6) * (k + 5)) * (3 - 1) ^ (k + 5) := by
      have := Nat.mul_le_mul_right (2 ^ (k + 5)) (aux_crossA k)
      calc 8 ^ (k + 5) * (k + 6) * (3 + 1) ^ (3 * (k + 5))
          = 2 ^ (8 * (k + 5)) * (k + 6) * 2 ^ (k + 5) := by
            rw [show (8 : ℕ) = 2 ^ 3 by norm_num, show (3 + 1 : ℕ) = 2 ^ 2 by norm_num,
              ← pow_mul, ← pow_mul]
            ring_nf
        _ ≤ 3 ^ ((k + 6) * (k + 5)) * 2 ^ (k + 5) := this
        _ = 3 ^ ((k + 6) * (k + 5)) * (3 - 1) ^ (k + 5) := by norm_num
    calc ((q + 1) ^ (k + 5) * ordProj[2] (k + 6).factorial) ^ 3 * (k + 6)
        ≤ ((q + 1) ^ (k + 5) * 2 ^ (k + 5)) ^ 3 * (k + 6) := by gcongr
      _ = 8 ^ (k + 5) * (k + 6) * (q + 1) ^ (3 * (k + 5)) := by
          rw [mul_pow, ← pow_mul, ← pow_mul, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
          ring_nf
      _ ≤ q ^ ((k + 6) * (k + 5)) * (q - 1) ^ (k + 5) :=
        mul_succ_pow_le_of_le (q₀ := 3) (by norm_num) hq (by nlinarith) hbase

theorem critB {m q : ℕ} (hm : 2 ≤ m) (hq : 3 ≤ q) (h2 : m = 2 → 9 ≤ q) :
    ((q + 1) ^ m * 2 ^ m * ordProj[2] m.factorial) ^ 3 * 2 ≤
      q ^ (m ^ 2) * (q ^ (m ^ 2) * (q - 1) ^ m) := by
  rw [← mul_assoc, ← pow_add]
  rcases (by omega : m = 2 ∨ m = 3 ∨ 4 ≤ m) with rfl | rfl | h4
  · rw [show Nat.factorial 2 = 2 ^ 1 * 1 by decide, ordProj_two_pow_mul_odd (by decide)]
    calc ((q + 1) ^ 2 * 2 ^ 2 * 2 ^ 1) ^ 3 * 2 = 1024 * (q + 1) ^ 6 := by ring
      _ ≤ q ^ 8 * (q - 1) ^ 2 :=
        mul_succ_pow_le_of_le (q₀ := 9) (by norm_num) (h2 rfl) (by norm_num) (by norm_num)
      _ = q ^ (2 ^ 2 + 2 ^ 2) * (q - 1) ^ 2 := by norm_num
  · rw [ordProj_two_factorial_three]
    calc ((q + 1) ^ 3 * 2 ^ 3 * 2 ^ 1) ^ 3 * 2 = 8192 * (q + 1) ^ 9 := by ring
      _ ≤ q ^ 18 * (q - 1) ^ 3 :=
        mul_succ_pow_le_of_le (q₀ := 3) (by norm_num) hq (by norm_num) (by norm_num)
      _ = q ^ (3 ^ 2 + 3 ^ 2) * (q - 1) ^ 3 := by norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
    have hW := ordProj_two_factorial_le (m := k + 4) (by omega)
    simp only [show k + 4 - 1 = k + 3 by omega] at hW
    have hbase : 2 ^ (6 * k + 22) * (3 + 1) ^ (3 * (k + 4)) ≤
        3 ^ ((k + 4) ^ 2 + (k + 4) ^ 2) * (3 - 1) ^ (k + 4) := by
      have := Nat.mul_le_mul_right (2 ^ (k + 4)) (aux_crossB k)
      calc 2 ^ (6 * k + 22) * (3 + 1) ^ (3 * (k + 4)) = 2 ^ (11 * k + 42) * 2 ^ (k + 4) := by
            rw [show (3 + 1 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add, ← pow_add]
            ring_nf
        _ ≤ 3 ^ (2 * (k + 4) ^ 2) * 2 ^ (k + 4) := this
        _ = 3 ^ ((k + 4) ^ 2 + (k + 4) ^ 2) * (3 - 1) ^ (k + 4) := by ring_nf
    calc ((q + 1) ^ (k + 4) * 2 ^ (k + 4) * ordProj[2] (k + 4).factorial) ^ 3 * 2
        ≤ ((q + 1) ^ (k + 4) * 2 ^ (k + 4) * 2 ^ (k + 3)) ^ 3 * 2 := by gcongr
      _ = 2 ^ (6 * k + 22) * (q + 1) ^ (3 * (k + 4)) := by
          rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
          ring_nf
      _ ≤ q ^ ((k + 4) ^ 2 + (k + 4) ^ 2) * (q - 1) ^ (k + 4) :=
        mul_succ_pow_le_of_le (q₀ := 3) (by norm_num) hq (by nlinarith) hbase

theorem critC {m q : ℕ} (hm : 4 ≤ m) (hq : 3 ≤ q) (h4 : m = 4 → 5 ≤ q) :
    ((q + 1) ^ m * 2 ^ (m - 1) * ordProj[2] m.factorial) ^ 3 * 4 ≤
      q ^ (m * (m - 1)) * (q ^ (m * (m - 1)) * (q - 1) ^ m) := by
  rw [← mul_assoc, ← pow_add]
  rcases (by omega : m = 4 ∨ 5 ≤ m) with rfl | h5
  · rw [ordProj_two_factorial_four]
    calc ((q + 1) ^ 4 * 2 ^ (4 - 1) * 2 ^ 3) ^ 3 * 4 = 1048576 * (q + 1) ^ 12 := by
          norm_num; ring
      _ ≤ q ^ 24 * (q - 1) ^ 4 :=
        mul_succ_pow_le_of_le (q₀ := 5) (by norm_num) (h4 rfl) (by norm_num) (by norm_num)
      _ = q ^ (4 * (4 - 1) + 4 * (4 - 1)) * (q - 1) ^ 4 := by norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 5 := ⟨m - 5, by omega⟩
    have hW := ordProj_two_factorial_le (m := k + 5) (by omega)
    simp only [show k + 5 - 1 = k + 4 by omega] at hW ⊢
    have hbase : 2 ^ (6 * k + 26) * (3 + 1) ^ (3 * (k + 5)) ≤
        3 ^ ((k + 5) * (k + 4) + (k + 5) * (k + 4)) * (3 - 1) ^ (k + 5) := by
      have := Nat.mul_le_mul_right (2 ^ (k + 5)) (aux_crossC k)
      calc 2 ^ (6 * k + 26) * (3 + 1) ^ (3 * (k + 5)) = 2 ^ (11 * k + 51) * 2 ^ (k + 5) := by
            rw [show (3 + 1 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add, ← pow_add]
            ring_nf
        _ ≤ 3 ^ (2 * ((k + 5) * (k + 4))) * 2 ^ (k + 5) := this
        _ = 3 ^ ((k + 5) * (k + 4) + (k + 5) * (k + 4)) * (3 - 1) ^ (k + 5) := by ring_nf
    calc ((q + 1) ^ (k + 5) * 2 ^ (k + 4) * ordProj[2] (k + 5).factorial) ^ 3 * 4
        ≤ ((q + 1) ^ (k + 5) * 2 ^ (k + 4) * 2 ^ (k + 4)) ^ 3 * 4 := by gcongr
      _ = 2 ^ (6 * k + 26) * (q + 1) ^ (3 * (k + 5)) := by
          rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
          ring_nf
      _ ≤ q ^ ((k + 5) * (k + 4) + (k + 5) * (k + 4)) * (q - 1) ^ (k + 5) :=
        mul_succ_pow_le_of_le (q₀ := 3) (by norm_num) hq (by nlinarith) hbase

section Families

variable {q n M : ℕ}

theorem odd_PSL (hq : 3 ≤ q) (hqodd : Odd q) (hn : 3 ≤ n) (h3 : n = 3 → 9 ≤ q)
    (h4 : n = 4 → 7 ≤ q)
    (hM : M * lieOrderDivisor .PSL n q = q ^ lieSylowExponent .PSL n * lieOrderCofactor .PSL n q) :
    ordProj[2] M ^ 3 ≤ M := by
  have hb := twoPartBound_prod_Icc_two (q := q) (fun i => q ^ i - 1)
    (fun i hi => twoPartBound_pow_sub_one' hq hqodd hi) (m := n) (by omega)
  exact ordProj_cube_le_of_twoPartBound hqodd hb (critA hn hq h3 h4) hM
    (Nat.gcd_pos_of_pos_left _ (by omega)) (Nat.gcd_le_left _ (by omega))

theorem odd_PSU (hq : 3 ≤ q) (hqodd : Odd q) (hn : 3 ≤ n) (h3 : n = 3 → 9 ≤ q)
    (h4 : n = 4 → 7 ≤ q)
    (hM : M * lieOrderDivisor .PSU n q = q ^ lieSylowExponent .PSU n * lieOrderCofactor .PSU n q) :
    ordProj[2] M ^ 3 ≤ M := by
  have hb := twoPartBound_prod_Icc_two (q := q)
    (fun i => if Even i then q ^ i - 1 else q ^ i + 1)
    (fun i hi => twoPartBound_psu_factor hq hqodd hi) (m := n) (by omega)
  exact ordProj_cube_le_of_twoPartBound hqodd hb (critA hn hq h3 h4) hM
    (Nat.gcd_pos_of_pos_left _ (by omega)) (Nat.gcd_le_left _ (by omega))

theorem odd_PSp (hq : 3 ≤ q) (hqodd : Odd q) (hn : 2 ≤ n) (h2 : n = 2 → 9 ≤ q)
    (hM : M * lieOrderDivisor .PSp n q = q ^ lieSylowExponent .PSp n * lieOrderCofactor .PSp n q) :
    ordProj[2] M ^ 3 ≤ M :=
  ordProj_cube_le_of_twoPartBound hqodd (twoPartBound_prod_Icc_one hq hqodd n) (critB hn hq h2)
    hM (Nat.gcd_pos_of_pos_left _ (by omega)) (Nat.gcd_le_left _ (by omega))

theorem odd_POmegaOdd (hq : 3 ≤ q) (hqodd : Odd q) (hn : 3 ≤ n)
    (hM : M * lieOrderDivisor .POmegaOdd n q =
      q ^ lieSylowExponent .POmegaOdd n * lieOrderCofactor .POmegaOdd n q) :
    ordProj[2] M ^ 3 ≤ M :=
  ordProj_cube_le_of_twoPartBound hqodd (twoPartBound_prod_Icc_one hq hqodd n)
    (critB (by omega) hq (fun h => by omega)) hM (by norm_num [lieOrderDivisor])
    (by norm_num [lieOrderDivisor])

theorem odd_POmegaPlus (hq : 3 ≤ q) (hqodd : Odd q) (hn : 4 ≤ n) (h4 : n = 4 → 5 ≤ q)
    (hM : M * lieOrderDivisor .POmegaPlus n q =
      q ^ lieSylowExponent .POmegaPlus n * lieOrderCofactor .POmegaPlus n q) :
    ordProj[2] M ^ 3 ≤ M :=
  ordProj_cube_le_of_twoPartBound hqodd
    (twoPartBound_omega hq hqodd (by omega) (twoPartBound_pow_sub_one' hq hqodd (by omega)))
    (critC hn hq h4) hM (Nat.gcd_pos_of_pos_left _ (by norm_num)) (Nat.gcd_le_left _ (by norm_num))

theorem odd_POmegaMinus (hq : 3 ≤ q) (hqodd : Odd q) (hn : 4 ≤ n) (h4 : n = 4 → 5 ≤ q)
    (hM : M * lieOrderDivisor .POmegaMinus n q =
      q ^ lieSylowExponent .POmegaMinus n * lieOrderCofactor .POmegaMinus n q) :
    ordProj[2] M ^ 3 ≤ M :=
  ordProj_cube_le_of_twoPartBound hqodd
    (twoPartBound_omega hq hqodd (by omega) ((twoPartBound_pow_add_one hq hqodd (a := n)
      (by omega)).mono le_rfl (Nat.le_mul_of_pos_right _ (by positivity))))
    (critC hn hq h4) hM (Nat.gcd_pos_of_pos_left _ (by norm_num)) (Nat.gcd_le_left _ (by norm_num))

end Families

section Exceptional

variable {q n M : ℕ}

theorem odd_G2 (hq : 3 ≤ q) (hqodd : Odd q)
    (hM : M * lieOrderDivisor .G2 n q = q ^ lieSylowExponent .G2 n * lieOrderCofactor .G2 n q) :
    ordProj[2] M ^ 3 ≤ M := by
  have hb := (twoPartBound_pow_sub_one_of_eq hq hqodd 6 5 1 3 rfl rfl (by decide)).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 2 1 1 1 rfl rfl (by decide))
  have hb' : TwoPartBound ((q ^ 6 - 1) * (q ^ 2 - 1)) (q ^ 6 * (q - 1) ^ 2)
      ((q + 1) ^ 2 * 2 ^ 2) := hb.mono (le_of_eq (by ring)) (le_of_eq (by ring))
  refine ordProj_cube_le_of_twoPartBound (G := 1) hqodd hb' ?_ hM
    (by norm_num [lieOrderDivisor]) (by norm_num [lieOrderDivisor])
  calc ((q + 1) ^ 2 * 2 ^ 2) ^ 3 * 1 = 64 * (q + 1) ^ 6 := by ring
    _ ≤ q ^ 12 * (q - 1) ^ 2 :=
      mul_succ_pow_le_of_le (q₀ := 3) (by norm_num) hq (by norm_num) (by norm_num)
    _ = q ^ 6 * (q ^ 6 * (q - 1) ^ 2) := by ring

theorem odd_F4 (hq : 3 ≤ q) (hqodd : Odd q)
    (hM : M * lieOrderDivisor .F4 n q = q ^ lieSylowExponent .F4 n * lieOrderCofactor .F4 n q) :
    ordProj[2] M ^ 3 ≤ M := by
  have hb := (((twoPartBound_pow_sub_one_of_eq hq hqodd 12 11 2 3 rfl rfl (by decide)).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 8 7 3 1 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 6 5 1 3 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 2 1 1 1 rfl rfl (by decide))
  have hb' : TwoPartBound ((q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1))
      (q ^ 24 * (q - 1) ^ 4) ((q + 1) ^ 4 * 2 ^ 7) :=
    hb.mono (le_of_eq (by ring)) (le_of_eq (by ring))
  refine ordProj_cube_le_of_twoPartBound (G := 1) hqodd hb' ?_ hM
    (by norm_num [lieOrderDivisor]) (by norm_num [lieOrderDivisor])
  calc ((q + 1) ^ 4 * 2 ^ 7) ^ 3 * 1 = 2 ^ 21 * (q + 1) ^ 12 := by ring
    _ ≤ q ^ 48 * (q - 1) ^ 4 :=
      mul_succ_pow_le_of_le (q₀ := 3) (by norm_num) hq (by norm_num) (by norm_num)
    _ = q ^ 24 * (q ^ 24 * (q - 1) ^ 4) := by ring

theorem odd_E6 (hq : 3 ≤ q) (hqodd : Odd q)
    (hM : M * lieOrderDivisor .E6 n q = q ^ lieSylowExponent .E6 n * lieOrderCofactor .E6 n q) :
    ordProj[2] M ^ 3 ≤ M := by
  have hb := (((((twoPartBound_pow_sub_one_of_eq hq hqodd 12 11 2 3 rfl rfl (by decide)).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 9 8 0 9 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 8 7 3 1 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 6 5 1 3 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 5 4 0 5 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 2 1 1 1 rfl rfl (by decide))
  have hb' : TwoPartBound ((q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 - 1) * (q ^ 2 - 1)) (q ^ 36 * (q - 1) ^ 6) ((q + 1) ^ 6 * 2 ^ 7) :=
    hb.mono (le_of_eq (by ring)) (le_of_eq (by ring))
  refine ordProj_cube_le_of_twoPartBound (G := 3) hqodd hb' ?_ hM
    (Nat.gcd_pos_of_pos_left _ (by norm_num)) (Nat.gcd_le_left _ (by norm_num))
  calc ((q + 1) ^ 6 * 2 ^ 7) ^ 3 * 3 = 3 * 2 ^ 21 * (q + 1) ^ 18 := by ring
    _ ≤ q ^ 72 * (q - 1) ^ 6 :=
      mul_succ_pow_le_of_le (q₀ := 3) (by norm_num) hq (by norm_num) (by norm_num)
    _ = q ^ 36 * (q ^ 36 * (q - 1) ^ 6) := by ring

theorem odd_twistedE6 (hq : 3 ≤ q) (hqodd : Odd q)
    (hM : M * lieOrderDivisor .twistedE6 n q =
      q ^ lieSylowExponent .twistedE6 n * lieOrderCofactor .twistedE6 n q) :
    ordProj[2] M ^ 3 ≤ M := by
  have hb := (((((twoPartBound_pow_sub_one_of_eq hq hqodd 12 11 2 3 rfl rfl (by decide)).mul
    (twoPartBound_pow_add_one_of_eq hq hqodd 9 8 rfl)).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 8 7 3 1 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 6 5 1 3 rfl rfl (by decide))).mul
    (twoPartBound_pow_add_one_of_eq hq hqodd 5 4 rfl)).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 2 1 1 1 rfl rfl (by decide))
  have hb' : TwoPartBound ((q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1)) (q ^ 36 * (q - 1) ^ 6) ((q + 1) ^ 6 * 2 ^ 7) :=
    hb.mono (le_of_eq (by ring)) (le_of_eq (by ring))
  refine ordProj_cube_le_of_twoPartBound (G := 3) hqodd hb' ?_ hM
    (Nat.gcd_pos_of_pos_left _ (by norm_num)) (Nat.gcd_le_left _ (by norm_num))
  calc ((q + 1) ^ 6 * 2 ^ 7) ^ 3 * 3 = 3 * 2 ^ 21 * (q + 1) ^ 18 := by ring
    _ ≤ q ^ 72 * (q - 1) ^ 6 :=
      mul_succ_pow_le_of_le (q₀ := 3) (by norm_num) hq (by norm_num) (by norm_num)
    _ = q ^ 36 * (q ^ 36 * (q - 1) ^ 6) := by ring

theorem odd_E7 (hq : 3 ≤ q) (hqodd : Odd q)
    (hM : M * lieOrderDivisor .E7 n q = q ^ lieSylowExponent .E7 n * lieOrderCofactor .E7 n q) :
    ordProj[2] M ^ 3 ≤ M := by
  have hb := ((((((twoPartBound_pow_sub_one_of_eq hq hqodd 18 17 1 9 rfl rfl (by decide)).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 14 13 1 7 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 12 11 2 3 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 10 9 1 5 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 8 7 3 1 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 6 5 1 3 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 2 1 1 1 rfl rfl (by decide))
  have hb' : TwoPartBound ((q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) *
      (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) (q ^ 63 * (q - 1) ^ 7) ((q + 1) ^ 7 * 2 ^ 10) :=
    hb.mono (le_of_eq (by ring)) (le_of_eq (by ring))
  refine ordProj_cube_le_of_twoPartBound (G := 2) hqodd hb' ?_ hM
    (Nat.gcd_pos_of_pos_left _ (by norm_num)) (Nat.gcd_le_left _ (by norm_num))
  calc ((q + 1) ^ 7 * 2 ^ 10) ^ 3 * 2 = 2 ^ 31 * (q + 1) ^ 21 := by ring
    _ ≤ q ^ 126 * (q - 1) ^ 7 :=
      mul_succ_pow_le_of_le (q₀ := 3) (by norm_num) hq (by norm_num) (by norm_num)
    _ = q ^ 63 * (q ^ 63 * (q - 1) ^ 7) := by ring

theorem odd_E8 (hq : 3 ≤ q) (hqodd : Odd q)
    (hM : M * lieOrderDivisor .E8 n q = q ^ lieSylowExponent .E8 n * lieOrderCofactor .E8 n q) :
    ordProj[2] M ^ 3 ≤ M := by
  have hb := (((((((twoPartBound_pow_sub_one_of_eq hq hqodd 30 29 1 15 rfl rfl
      (by decide)).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 24 23 3 3 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 20 19 2 5 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 18 17 1 9 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 14 13 1 7 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 12 11 2 3 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 8 7 3 1 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 2 1 1 1 rfl rfl (by decide))
  have hb' : TwoPartBound ((q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) *
      (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)) (q ^ 120 * (q - 1) ^ 8)
      ((q + 1) ^ 8 * 2 ^ 14) :=
    hb.mono (le_of_eq (by ring)) (le_of_eq (by ring))
  refine ordProj_cube_le_of_twoPartBound (G := 1) hqodd hb' ?_ hM
    (by norm_num [lieOrderDivisor]) (by norm_num [lieOrderDivisor])
  calc ((q + 1) ^ 8 * 2 ^ 14) ^ 3 * 1 = 2 ^ 42 * (q + 1) ^ 24 := by ring
    _ ≤ q ^ 240 * (q - 1) ^ 8 :=
      mul_succ_pow_le_of_le (q₀ := 3) (by norm_num) hq (by norm_num) (by norm_num)
    _ = q ^ 120 * (q ^ 120 * (q - 1) ^ 8) := by ring

theorem odd_trialityD4 (hq : 3 ≤ q) (hqodd : Odd q)
    (hM : M * lieOrderDivisor .trialityD4 n q =
      q ^ lieSylowExponent .trialityD4 n * lieOrderCofactor .trialityD4 n q) :
    ordProj[2] M ^ 3 ≤ M := by
  have hb := ((twoPartBound_triality hqodd).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 6 5 1 3 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 2 1 1 1 rfl rfl (by decide))
  have hb' : TwoPartBound ((q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1))
      (q ^ 14 * (q - 1) ^ 2) ((q + 1) ^ 2 * 2 ^ 2) :=
    hb.mono (le_of_eq (by ring)) (le_of_eq (by ring))
  refine ordProj_cube_le_of_twoPartBound (G := 1) hqodd hb' ?_ hM
    (by norm_num [lieOrderDivisor]) (by norm_num [lieOrderDivisor])
  calc ((q + 1) ^ 2 * 2 ^ 2) ^ 3 * 1 = 64 * (q + 1) ^ 6 := by ring
    _ ≤ q ^ 26 * (q - 1) ^ 2 :=
      mul_succ_pow_le_of_le (q₀ := 3) (by norm_num) hq (by norm_num) (by norm_num)
    _ = q ^ 12 * (q ^ 14 * (q - 1) ^ 2) := by ring

theorem odd_twistedG2 (hq : 27 ≤ q) (hqodd : Odd q)
    (hM : M * lieOrderDivisor .twistedG2 n q =
      q ^ lieSylowExponent .twistedG2 n * lieOrderCofactor .twistedG2 n q) :
    ordProj[2] M ^ 3 ≤ M := by
  have hq3 : 3 ≤ q := by omega
  have h1 := twoPartBound_pow_sub_one_of_eq hq3 hqodd 1 0 0 1 rfl rfl odd_one
  rw [pow_one] at h1
  have hb := (twoPartBound_pow_add_one_of_eq hq3 hqodd 3 2 rfl).mul h1
  have hb' : TwoPartBound ((q ^ 3 + 1) * (q - 1)) (q ^ 2 * (q - 1) ^ 2) ((q + 1) ^ 2) :=
    hb.mono (le_of_eq (by ring)) (le_of_eq (by ring))
  refine ordProj_cube_le_of_twoPartBound (G := 1) hqodd hb' ?_ hM
    (by norm_num [lieOrderDivisor]) (by norm_num [lieOrderDivisor])
  calc ((q + 1) ^ 2) ^ 3 * 1 = 1 * (q + 1) ^ 6 := by ring
    _ ≤ q ^ 5 * (q - 1) ^ 2 :=
      mul_succ_pow_le_of_le (q₀ := 27) (by norm_num) hq (by norm_num) (by norm_num)
    _ = q ^ 3 * (q ^ 2 * (q - 1) ^ 2) := by ring

end Exceptional

theorem ordProj_two_cube_le_of_odd {t : StatedLieTag} {n p f M : ℕ}
    (hadm : StatedLieAdmissible t n p f) (hp2 : p ≠ 2)
    (hM : M * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f)) :
    ordProj[2] M ^ 3 ≤ M ∨ (t = .PSL ∧ n = 2) ∨ (t = .PSU ∧ n = 3 ∧ p ^ f = 3 ∧ M = 6048) ∨
      (t = .PSp ∧ n = 2 ∧ p ^ f = 3 ∧ M = 25920) := by
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    obtain ⟨k, hk⟩ := hpodd
    omega
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hq3 : 3 ≤ p ^ f := hp3.trans (Nat.le_self_pow (by omega) p)
  rw [lieOrderNumerator_eq hadm] at hM
  obtain ⟨q, hq⟩ : ∃ q, p ^ f = q := ⟨_, rfl⟩
  rw [hq] at hM hqodd hq3 ⊢
  have hq2 : q % 2 = 1 := Nat.odd_iff.mp hqodd
  cases t
  case PSL =>
    obtain ⟨-, -, hn, -, -⟩ := hadm
    rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    left
    by_cases hs : (n = 3 ∧ q < 9) ∨ (n = 4 ∧ q < 7)
    · rcases hs with ⟨rfl, hq9⟩ | ⟨rfl, hq7⟩
      · rcases (by omega : q = 3 ∨ q = 5 ∨ q = 7) with rfl | rfl | rfl
        · exact ordProj_cube_le_of_eq (k := 4) (r := 351) (by rw [hM]; decide) (by decide)
            (by decide) (by norm_num)
        · exact ordProj_cube_le_of_eq (k := 5) (r := 11625) (by rw [hM]; decide) (by decide)
            (by decide) (by norm_num)
        · exact ordProj_cube_le_of_eq (k := 5) (r := 58653) (by rw [hM]; decide) (by decide)
            (by decide) (by norm_num)
      · rcases (by omega : q = 3 ∨ q = 5) with rfl | rfl
        · exact ordProj_cube_le_of_eq (k := 7) (r := 47385) (by rw [hM]; decide) (by decide)
            (by decide) (by norm_num)
        · exact ordProj_cube_le_of_eq (k := 7) (r := 56671875) (by rw [hM]; decide)
            (by decide) (by decide) (by norm_num)
    · push Not at hs
      exact odd_PSL hq3 hqodd hn3 hs.1 hs.2 hM
  case PSU =>
    obtain ⟨-, -, hn, -⟩ := hadm
    by_cases hs : (n = 3 ∧ q < 9) ∨ (n = 4 ∧ q < 7)
    · rcases hs with ⟨rfl, hq9⟩ | ⟨rfl, hq7⟩
      · rcases (by omega : q = 3 ∨ q = 5 ∨ q = 7) with rfl | rfl | rfl
        · refine Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, ?_⟩))
          exact eq_of_mul_eq_mul (hM.trans (by decide)) (by decide)
        · exact Or.inl (ordProj_cube_le_of_eq (k := 4) (r := 7875) (by rw [hM]; decide)
            (by decide) (by decide) (by norm_num))
        · exact Or.inl (ordProj_cube_le_of_eq (k := 7) (r := 44247) (by rw [hM]; decide)
            (by decide) (by decide) (by norm_num))
      · rcases (by omega : q = 3 ∨ q = 5) with rfl | rfl
        · exact Or.inl (ordProj_cube_le_of_eq (k := 7) (r := 25515) (by rw [hM]; decide)
            (by decide) (by decide) (by norm_num))
        · exact Or.inl (ordProj_cube_le_of_eq (k := 7) (r := 115171875) (by rw [hM]; decide)
            (by decide) (by decide) (by norm_num))
    · push Not at hs
      exact Or.inl (odd_PSU hq3 hqodd hn hs.1 hs.2 hM)
  case PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    by_cases hs : n = 2 ∧ q < 9
    · obtain ⟨rfl, hq9⟩ := hs
      rcases (by omega : q = 3 ∨ q = 5 ∨ q = 7) with rfl | rfl | rfl
      · refine Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, ?_⟩))
        exact eq_of_mul_eq_mul (hM.trans (by decide)) (by decide)
      · exact Or.inl (ordProj_cube_le_of_eq (k := 6) (r := 73125) (by rw [hM]; decide)
          (by decide) (by decide) (by norm_num))
      · exact Or.inl (ordProj_cube_le_of_eq (k := 8) (r := 540225) (by rw [hM]; decide)
          (by decide) (by decide) (by norm_num))
    · exact Or.inl (odd_PSp hq3 hqodd hn (fun h => by omega) hM)
  case POmegaOdd =>
    obtain ⟨-, -, hn, -⟩ := hadm
    exact Or.inl (odd_POmegaOdd hq3 hqodd hn hM)
  case POmegaPlus =>
    obtain ⟨-, -, hn⟩ := hadm
    by_cases hs : n = 4 ∧ q < 5
    · obtain ⟨rfl, hq5⟩ := hs
      obtain rfl : q = 3 := by omega
      exact Or.inl (ordProj_cube_le_of_eq (k := 12) (r := 1209028275) (by rw [hM]; decide)
        (by decide) (by decide) (by norm_num))
    · exact Or.inl (odd_POmegaPlus hq3 hqodd hn (fun h => by omega) hM)
  case POmegaMinus =>
    obtain ⟨-, -, hn⟩ := hadm
    by_cases hs : n = 4 ∧ q < 5
    · obtain ⟨rfl, hq5⟩ := hs
      obtain rfl : q = 3 := by omega
      exact Or.inl (ordProj_cube_le_of_eq (k := 10) (r := 9914031855) (by rw [hM]; decide)
        (by decide) (by decide) (by norm_num))
    · exact Or.inl (odd_POmegaMinus hq3 hqodd hn (fun h => by omega) hM)
  case G2 => exact Or.inl (odd_G2 hq3 hqodd hM)
  case F4 => exact Or.inl (odd_F4 hq3 hqodd hM)
  case E6 => exact Or.inl (odd_E6 hq3 hqodd hM)
  case E7 => exact Or.inl (odd_E7 hq3 hqodd hM)
  case E8 => exact Or.inl (odd_E8 hq3 hqodd hM)
  case twistedE6 => exact Or.inl (odd_twistedE6 hq3 hqodd hM)
  case trialityD4 => exact Or.inl (odd_trialityD4 hq3 hqodd hM)
  case twistedB2 => exact absurd hadm.2.2.2.1 hp2
  case twistedF4 => exact absurd hadm.2.2.2.1 hp2
  case Tits => exact absurd hadm.2.2.2.1 hp2
  case twistedG2 =>
    obtain ⟨-, -, -, rfl, -, hf3⟩ := hadm
    have h27 : 27 ≤ q := by
      rw [← hq]
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
    exact Or.inl (odd_twistedG2 h27 hqodd hM)

end CFSG.SeitzReduction.CrossChar
