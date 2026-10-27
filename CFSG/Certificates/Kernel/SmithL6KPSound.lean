module

public import CFSG.Certificates.Kernel.SmithL6KMeet
public import Certificates.Data.Kernel.SmithL6KP
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6
open Finset

theorem exists_low_bit : ∀ n : Nat, n ≠ 0 → ∃ k q, n = 2 ^ (k + 1) * q + 2 ^ k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h2 : n % 2 = 0
    · obtain ⟨k, q, e⟩ := ih (n / 2) (by omega) (by omega)
      refine ⟨k + 1, q, ?_⟩
      have hn2 : n = 2 * (n / 2) := by omega
      rw [hn2, e]
      ring
    · exact ⟨0, n / 2, by omega⟩

theorem testBit_and_sub_one (k q j : Nat) :
    ((2 ^ (k + 1) * q + 2 ^ k) &&& (2 ^ (k + 1) * q + 2 ^ k - 1)).testBit j =
      ((2 ^ (k + 1) * q + 2 ^ k).testBit j && decide (j ≠ k)) := by
  have hk : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h1 : 2 ^ (k + 1) * q + 2 ^ k - 1 = 2 ^ (k + 1) * q + (2 ^ k - 1) := by
    generalize 2 ^ (k + 1) * q = A at *
    omega
  rw [Nat.testBit_and, h1, Nat.testBit_two_pow_mul_add q hk,
    Nat.testBit_two_pow_mul_add q (b := 2 ^ k - 1) (by omega), Nat.testBit_two_pow,
    Nat.testBit_two_pow_sub_one]
  by_cases hj : j < k + 1
  · rw [if_pos hj, if_pos hj]
    by_cases hjk : j = k
    · subst hjk
      simp
    · have : j < k := by omega
      simp [hjk, this, Ne.symm hjk]
  · rw [if_neg hj, if_neg hj]
    have : j ≠ k := by omega
    simp [this]

theorem setM_zero : setM 0 = ∅ := by
  ext x
  simp [mem_setM]

theorem card_and_sub_one (n : Nat) : (setM (n &&& (n - 1))).card = (setM n).card - 1 := by
  by_cases hn : n = 0
  · subst hn
    rw [Nat.zero_and, setM_zero]
    rfl
  · obtain ⟨k, q, rfl⟩ := exists_low_bit n hn
    have e : setM ((2 ^ (k + 1) * q + 2 ^ k) &&& (2 ^ (k + 1) * q + 2 ^ k - 1)) =
        (setM (2 ^ (k + 1) * q + 2 ^ k)).erase k := by
      ext x
      rw [Finset.mem_erase, mem_setM, mem_setM, testBit_and_sub_one]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      tauto
    rw [e, Finset.card_erase_eq_ite]
    split_ifs with h
    · rfl
    · have hk : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
      have hbit : (2 ^ (k + 1) * q + 2 ^ k).testBit k = true := by
        rw [Nat.testBit_two_pow_mul_add q hk, if_pos (by omega), Nat.testBit_two_pow]
        simp
      have h64 : 64 ≤ k := by
        by_contra hlt
        exact h (mem_setM.mpr ⟨by omega, hbit⟩)
      have e0 : setM (2 ^ (k + 1) * q + 2 ^ k) = ∅ := by
        ext x
        rw [mem_setM, Nat.testBit_two_pow_mul_add q hk]
        constructor
        · rintro ⟨hx, hb⟩
          rw [if_pos (by omega), Nat.testBit_two_pow] at hb
          simp only [decide_eq_true_eq] at hb
          omega
        · simp
      rw [e0]
      rfl

theorem eq_zero_of_setM {x : Nat} (hx : x < 2 ^ 64) (h : setM x = ∅) : x = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.zero_testBit]
  by_cases hj : j < 64
  · cases hb : x.testBit j
    · rfl
    · have : j ∈ setM x := mem_setM.mpr ⟨hj, hb⟩
      rw [h] at this
      simp at this
  · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))

theorem atLeast4_iff {n : Nat} (hn : n < 2 ^ 64) : atLeast4 n = true ↔ 4 ≤ (setM n).card := by
  unfold atLeast4
  simp only [bne_iff_ne, ne_eq]
  have c1 := card_and_sub_one n
  have c2 := card_and_sub_one (n &&& (n - 1))
  have c3 := card_and_sub_one ((n &&& (n - 1)) &&& ((n &&& (n - 1)) - 1))
  generalize hn1 : n &&& (n - 1) = n1 at c1 c2 c3
  generalize hn2 : n1 &&& (n1 - 1) = n2 at c2 c3
  generalize hn3 : n2 &&& (n2 - 1) = n3 at c3
  have l3 : n3 < 2 ^ 64 := by
    have a1 : n1 ≤ n := hn1 ▸ Nat.and_le_left
    have a2 : n2 ≤ n1 := hn2 ▸ Nat.and_le_left
    have a3 : n3 ≤ n2 := hn3 ▸ Nat.and_le_left
    omega
  constructor
  · intro h
    have hne : (setM n3).card ≠ 0 := fun h0 => h (eq_zero_of_setM l3 (Finset.card_eq_zero.mp h0))
    omega
  · intro h h0
    rw [h0, setM_zero] at c3
    simp only [Finset.card_empty] at c3
    omega

theorem twoB_iff {x : Nat} (hx : x < 2 ^ 64) (hX : XorClosed (setM x)) (h8 : (setM x).card ≤ 8) :
    twoB x = true ↔ (setM x).card = 2 := by
  unfold twoB
  rw [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true', ← Bool.not_eq_true, atLeast4_iff hx]
  have h1 : x = 1 ↔ (setM x).card = 1 := by
    constructor
    · rintro rfl
      decide
    · intro hc
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
      have h0 := hX.2.1
      rw [ha, Finset.mem_singleton] at h0
      subst h0
      apply Nat.eq_of_testBit_eq
      intro j
      have e2 : (1 : Nat) = 2 ^ 0 := rfl
      rw [e2, Nat.testBit_two_pow]
      by_cases hj0 : j = 0
      · subst hj0
        have : 0 ∈ setM x := by rw [ha]; simp
        rw [(mem_setM.mp this).2]
        rfl
      · rw [decide_eq_false (Ne.symm hj0)]
        by_cases hj : j < 64
        · cases hb : x.testBit j
          · rfl
          · have : j ∈ setM x := mem_setM.mpr ⟨hj, hb⟩
            rw [ha, Finset.mem_singleton] at this
            exact absurd this hj0
        · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx
            (Nat.pow_le_pow_right (by omega) (by omega)))
  rw [ne_eq, h1]
  rcases card_pow2 hX h8 with h | h | h | h <;> rw [h] <;> decide

theorem spanMask_lt {a b c : Nat} (ha : a < 64) (hb : b < 64) (hc : c < 64) :
    spanMask a b c < 2 ^ 64 := by
  refine Nat.lt_pow_two_of_testBit _ fun j hj => ?_
  rw [spanMask_testBit, Bool.eq_false_iff]
  intro h
  rw [List.any_eq_true] at h
  obtain ⟨d, -, hd⟩ := h
  have := comb_lt ha hb hc d
  rw [beq_iff_eq] at hd
  omega

end CFSG.SmithL6.K
