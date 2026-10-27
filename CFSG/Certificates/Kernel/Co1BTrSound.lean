module

public import CFSG.Certificates.Kernel.Co1BMulSound

public section

namespace CFSG.KC.F2W

open CFSG.KC.Loop CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.Sporadic.SmallF2.Native

theorem testBit_ofBitsFold (f : Nat → Bool) (k : Nat) : ∀ n : Nat,
    ((List.range n).foldl (fun acc j => if f j then acc ||| (1 <<< j) else acc) 0).testBit k =
      (decide (k < n) && f k)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have ih := testBit_ofBitsFold f k n
    by_cases hk : k = n
    · subst hk
      cases h : f k
      · simp only [h, Bool.false_eq_true, ↓reduceIte, ih]
        simp
      · simp only [h, ↓reduceIte, Nat.testBit_or, ih, Nat.testBit_shiftLeft, testBit_one_eq]
        simp
    · cases f n
      · simp only [Bool.false_eq_true, ↓reduceIte, ih]
        by_cases hkn : k < n
        · simp [hkn, show k < n + 1 by omega]
        · simp [hkn, show ¬ k < n + 1 by omega]
      · simp only [↓reduceIte, Nat.testBit_or, ih, Nat.testBit_shiftLeft, testBit_one_eq]
        by_cases hkn : k < n
        · simp [hkn, show k < n + 1 by omega]
        · have : ¬ k < n + 1 := by omega
          simp [hkn, this]
          omega

theorem testBit_orN_bits (c : Nat → Bool) (k : Nat) : ∀ n : Nat,
    (orN n fun i => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (pw2 i) (c i)).testBit k =
      (decide (k < n) && c k)
  | 0 => by simp [orN_zero]
  | n + 1 => by
    rw [orN_succ, Nat.testBit_or, testBit_orN_bits c k n]
    have hp : ∀ i, pw2 i = 1 <<< i := fun _ => rfl
    by_cases hk : k = n
    · subst hk
      cases c k
      · simp
      · simp [hp, Nat.testBit_shiftLeft]
    · cases h : c n
      · by_cases hkn : k < n
        · simp [hkn, show k < n + 1 by omega]
        · simp [hkn, show ¬ k < n + 1 by omega]
      · simp only [hp, Nat.testBit_shiftLeft, testBit_one_eq]
        by_cases hkn : k < n
        · simp [hkn, show k < n + 1 by omega]
        · have : ¬ k < n + 1 := by omega
          simp [hkn, this]
          omega

theorem transposeRows_unpackR (d M : Nat) : transposeRows d (unpackR d M) = unpackR d (trK d M) := by
  have hlt : ∀ j, (orN d fun i => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (pw2 i)
      (bit M (Nat.add (Nat.mul d i) j))) < 2 ^ d := fun j =>
    Nat.lt_pow_two_of_testBit _ fun k hk => by rw [testBit_orN_bits]; simp [Nat.not_lt.2 hk]
  rw [transposeRows]
  conv_rhs => rw [unpackR]
  congr 1
  funext j
  rw [← rowF_eq]
  change _ = rowF d (orN d fun j => (orN d fun i => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (pw2 i)
      (bit M (Nat.add (Nat.mul d i) j))) <<< (d * j)) j
  rw [rowF_orN d (fun j _ => hlt j) j.isLt, ofBits]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_ofBitsFold, testBit_orN_bits, bit_eq]
  by_cases hk : k < d
  · simp only [hk, decide_true, Bool.true_and]
    have hget : (unpackR d M)[k]?.getD 0 = rowF d M k := by simp [unpackR, hk, rowF_eq]
    rw [hget, testBit_rowF d M k j j.isLt]
    change M.testBit (k * d + j) = M.testBit (d * k + j)
    rw [Nat.mul_comm]
  · simp [hk]

theorem act_unpackR {M T : Nat} (hT : trK 24 M = T) (v : Nat) :
    CFSG.Sporadic.Co1Schreier.Native.act (unpackR 24 M) v = vmF 24 T v := by
  rw [CFSG.Sporadic.Co1Schreier.Native.act, transposeRows_unpackR, hT, vecMulN_unpackR]

end CFSG.KC.F2W

end
