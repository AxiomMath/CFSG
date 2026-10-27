module

public import CFSG.Certificates.Kernel.Co1BMulSound
public import CFSG.LargeExtraspecial.S63CD4Check

public section

set_option exponentiation.threshold 600

namespace CFSG.KC.S63K

open CFSG.KC.Co1F2 CFSG.LargeExtraspecial.S63 CFSG.Sporadic.SmallF2.Native

@[expose] noncomputable def idP : Nat :=
  (List.range 24).foldr (fun i acc => Nat.lor (Nat.shiftLeft 1 (25 * i)) acc) 0

theorem unpackR_get (X : Nat) {i : Nat} (hi : i < 24) :
    (unpackR 24 X)[i]! = X / 2 ^ (24 * i) % 2 ^ 24 := by
  rw [getElem!_pos (unpackR 24 X) i (by simp [unpackR, hi])]
  simp [unpackR]

theorem unpackR_size (X : Nat) : (unpackR 24 X).size = 24 := by simp [unpackR]

theorem unpackR_mod (X : Nat) : unpackR 24 X = unpackR 24 (X % 2 ^ 576) := by
  apply Array.ext
  · simp [unpackR]
  · intro i h1 _
    have hi : i < 24 := by simpa [unpackR] using h1
    simp only [unpackR, Array.getElem_ofFn]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
      Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow]
    by_cases hj : j < 24
    · have : j + 24 * i < 576 := by omega
      simp [hj, this]
    · simp [hj]

theorem testBit_of_unpackR (X j : Nat) (hj : j < 576) :
    (X % 2 ^ 576).testBit j = ((unpackR 24 X)[j / 24]!).testBit (j % 24) := by
  rw [unpackR_get X (by omega), Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow]
  have e : j % 24 + 24 * (j / 24) = j := by omega
  simp [hj, Nat.mod_lt j (by norm_num : 0 < 24), e]

theorem unpackR_inj {A B : Nat} : unpackR 24 A = unpackR 24 B ↔ A % 2 ^ 576 = B % 2 ^ 576 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < 576
    · rw [testBit_of_unpackR A j hj, testBit_of_unpackR B j hj, h]
    · rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
      simp [hj]
  · intro h
    rw [unpackR_mod A, unpackR_mod B, h]

theorem beq_unpackR (A B : Nat) :
    (unpackR 24 A == unpackR 24 B) = Nat.beq (A % 2 ^ 576) (B % 2 ^ 576) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq, unpackR_inj]

theorem mulR_unpackR (A B : Nat) :
    mulR (unpackR 24 A) (unpackR 24 B) = unpackR 24 (CFSG.KC.F2W.mulW 24 A B) :=
  CFSG.KC.F2W.mulRows_unpackW 24 A B

theorem oneR_eq : oneR = unpackR 24 idP := by
  unfold oneR idRows
  apply Array.ext
  · simp [unpackR]
  · intro i h1 _
    have hi : i < 24 := by simpa using h1
    simp only [Array.getElem_ofFn, unpackR]
    interval_cases i <;> decide

theorem validR_unpackR (X : Nat) : validR (unpackR 24 X) = true := by
  unfold validR
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  refine ⟨unpackR_size X, fun i hi => ?_⟩
  rw [unpackR_get X hi]
  exact Nat.mod_lt _ (by norm_num)

end CFSG.KC.S63K

end
