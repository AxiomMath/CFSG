module

public import CFSG.Certificates.Kernel.O8UnitSound

public section

namespace CFSG.KC.O8

open CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem testBit_mulVecK_pow (k : ℕ) {i j : ℕ} (hi : i < 12) (hj : j < 12) :
    (mulVecK k (2 ^ j)).testBit i = k.testBit (12 * i + j) := by
  have e := congrFun (toVec_mulVecK k (2 ^ j)) ⟨i, hi⟩
  simp only [toVec, toMatK, Matrix.mulVec, dotProduct, Matrix.of_apply, Nat.testBit_two_pow] at e
  rw [Finset.sum_eq_single ⟨j, hj⟩ (fun l _ hl => by
      have hne : ¬ j = (l : ℕ) := fun h => hl (Fin.ext h.symm)
      simp [hne, bz]) (by simp)] at e
  simp only [decide_true] at e
  have e1 : bz true = 1 := rfl
  rw [e1, mul_one] at e
  exact bz_injective e

theorem mulVecK_pow_beq (k : ℕ) {j : ℕ} (hj : j < 12) :
    (mulVecK k (2 ^ j) == 2 ^ j) = ((k >>> j) &&& low12 == 2 ^ (12 * j)) := by
  apply Bool.eq_iff_iff.2
  simp only [beq_iff_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro q
    rw [Nat.testBit_and, low12_testBit, Nat.testBit_shiftRight, Nat.testBit_two_pow]
    by_cases hq : q < 144 ∧ q % 12 = 0
    · have hi : q / 12 < 12 := by omega
      have e := congrArg (fun x => Nat.testBit x (q / 12)) h
      rw [testBit_mulVecK_pow k hi hj, Nat.testBit_two_pow,
        show 12 * (q / 12) + j = j + q by omega] at e
      rw [e]
      simp only [hq, and_self, decide_true, Bool.and_true]
      apply Bool.eq_iff_iff.2
      simp only [decide_eq_true_eq]
      omega
    · have hne : ¬ 12 * j = q := by omega
      simp [hq, hne]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 12
    · rw [testBit_mulVecK_pow k hi hj, Nat.testBit_two_pow]
      have e := congrArg (fun x => Nat.testBit x (12 * i)) h
      rw [Nat.testBit_and, low12_testBit, Nat.testBit_shiftRight, Nat.testBit_two_pow] at e
      have h1 : 12 * i < 144 ∧ 12 * i % 12 = 0 := by omega
      simp only [h1, and_self, decide_true, Bool.and_true] at e
      rw [show 12 * i + j = j + 12 * i by omega, e]
      apply Bool.eq_iff_iff.2
      simp only [decide_eq_true_eq]
      omega
    · have hlt : mulVecK k (2 ^ j) < 2 ^ i :=
        lt_of_lt_of_le (mulVecK_lt k _) (by
          have := Nat.pow_le_pow_right (n := 2) (by norm_num) (show 12 ≤ i by omega)
          simpa using this)
      rw [Nat.testBit_lt_two_pow hlt, Nat.testBit_two_pow]
      have hne : ¬ j = i := by omega
      simp [hne]

theorem mulVecK_one_beq (k : ℕ) : (mulVecK k 1 == 1) = (k &&& low12 == 1) := by
  have h := mulVecK_pow_beq k (j := 0) (by norm_num)
  simp only [Nat.pow_zero, Nat.shiftRight_zero, Nat.mul_zero] at h
  exact h

theorem mulVecK_two_beq (k : ℕ) : (mulVecK k 2 == 2) = (k >>> 1 &&& low12 == 4096) := by
  have h := mulVecK_pow_beq k (j := 1) (by norm_num)
  simp only [Nat.pow_one, Nat.mul_one, Nat.reducePow] at h
  exact h

theorem mulVecK_sixteen_beq (k : ℕ) :
    (mulVecK k 16 == 16) = (k >>> 4 &&& low12 == 281474976710656) := by
  have h := mulVecK_pow_beq k (j := 4) (by norm_num)
  simp only [Nat.reduceMul, Nat.reducePow] at h
  exact h

theorem testBit_mulVecK_pow2 (k : ℕ) {i a b : ℕ} (hi : i < 12) (ha : a < 12) (hb : b < 12) :
    (mulVecK k (2 ^ a ^^^ 2 ^ b)).testBit i = (k.testBit (12 * i + a) ^^ k.testBit (12 * i + b)) := by
  rw [mulVecK_xor, Nat.testBit_xor, testBit_mulVecK_pow k hi ha, testBit_mulVecK_pow k hi hb]

theorem mulVecK_pow2_beq (k : ℕ) {a b : ℕ} (ha : a < 12) (hb : b < 12) :
    (mulVecK k (2 ^ a ^^^ 2 ^ b) == 2 ^ a ^^^ 2 ^ b) =
      ((k >>> a ^^^ k >>> b) &&& low12 == 2 ^ (12 * a) ^^^ 2 ^ (12 * b)) := by
  apply Bool.eq_iff_iff.2
  simp only [beq_iff_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro q
    rw [Nat.testBit_and, low12_testBit, Nat.testBit_xor, Nat.testBit_shiftRight,
      Nat.testBit_shiftRight, Nat.testBit_xor, Nat.testBit_two_pow, Nat.testBit_two_pow]
    by_cases hq : q < 144 ∧ q % 12 = 0
    · obtain ⟨i, rfl⟩ : ∃ i, q = 12 * i := ⟨q / 12, by omega⟩
      have hi : i < 12 := by omega
      have e := congrArg (fun x => Nat.testBit x i) h
      rw [testBit_mulVecK_pow2 k hi ha hb, Nat.testBit_xor, Nat.testBit_two_pow,
        Nat.testBit_two_pow] at e
      have e1 : 12 * a = 12 * i ↔ a = i := by omega
      have e2 : 12 * b = 12 * i ↔ b = i := by omega
      simp only [e1, e2]
      rw [← e, Nat.add_comm a, Nat.add_comm b]
      simp only [hq, and_self, decide_true, Bool.and_true]
    · have hne1 : ¬ 12 * a = q := by omega
      have hne2 : ¬ 12 * b = q := by omega
      simp [hq, hne1, hne2]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 12
    · rw [testBit_mulVecK_pow2 k hi ha hb, Nat.testBit_xor, Nat.testBit_two_pow,
        Nat.testBit_two_pow]
      have e := congrArg (fun x => Nat.testBit x (12 * i)) h
      rw [Nat.testBit_and, low12_testBit, Nat.testBit_xor, Nat.testBit_shiftRight,
        Nat.testBit_shiftRight, Nat.testBit_xor, Nat.testBit_two_pow, Nat.testBit_two_pow] at e
      have h1 : 12 * i < 144 ∧ 12 * i % 12 = 0 := by omega
      have e1 : 12 * a = 12 * i ↔ a = i := by omega
      have e2 : 12 * b = 12 * i ↔ b = i := by omega
      simp only [h1, and_self, decide_true, Bool.and_true, e1, e2] at e
      rw [Nat.add_comm (12 * i) a, Nat.add_comm (12 * i) b, e]
    · have hlt : mulVecK k (2 ^ a ^^^ 2 ^ b) < 2 ^ i :=
        lt_of_lt_of_le (mulVecK_lt k _) (by
          have := Nat.pow_le_pow_right (n := 2) (by norm_num) (show 12 ≤ i by omega)
          simpa using this)
      rw [Nat.testBit_lt_two_pow hlt, Nat.testBit_xor, Nat.testBit_two_pow, Nat.testBit_two_pow]
      have hne1 : ¬ a = i := by omega
      have hne2 : ¬ b = i := by omega
      simp [hne1, hne2]

theorem mulVecK_eighty_beq (k : ℕ) :
    (mulVecK k 80 == 80) = ((k >>> 4 ^^^ k >>> 6) &&& low12 == 4722366764344621924352) := by
  have h := mulVecK_pow2_beq k (a := 4) (b := 6) (by norm_num) (by norm_num)
  have e1 : (2 ^ 4 ^^^ 2 ^ 6 : ℕ) = 80 := by decide
  have e2 : (2 ^ (12 * 4) ^^^ 2 ^ (12 * 6) : ℕ) = 4722366764344621924352 := by decide
  rw [e1, e2] at h
  exact h

end CFSG.KC.O8

end
