module

public import CFSG.Certificates.Kernel.F2WordSound
public import CFSG.Certificates.Kernel.Co1F2Sound
public import Certificates.Data.CFSGNative.Co1Schreier.Base

public section

namespace CFSG.KC.F2W

open CFSG.KC.Loop CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.Sporadic.SmallF2.Native

theorem rowF_eq (d M i : Nat) : rowF d M i = M / 2 ^ (d * i) % 2 ^ d := by
  rw [rowF, fget, maskN_eq]
  change (M >>> (i * d)) &&& (2 ^ d - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.mul_comm i d]

theorem rowF_orN (d : Nat) {f : Nat → Nat} (hf : ∀ i < d, f i < 2 ^ d) {i : Nat} (hi : i < d) :
    rowF d (orN d fun i => f i <<< (d * i)) i = f i := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < d
  · rw [testBit_rowF _ _ _ _ hj, testBit_orN_fields hf]
    have hq : (i * d + j) / d = i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
    have hr : (i * d + j) % d = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    have hlt : i * d + j < d * d := by
      have : i * d + d ≤ d * d := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right d hi
      omega
    simp [hq, hr, hlt]
  · have h1 := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (rowF_lt d (orN d fun i => f i <<< (d * i)) i)
      (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hj)))
    have h2 := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hf i hi)
      (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hj)))
    rw [h1, h2]

theorem foldl_range_xor (g g' : Nat → Nat) (c : Nat → Bool) : ∀ n : Nat, (∀ j < n, g' j = g j) →
    (List.range n).foldl (fun acc j => if c j then acc ^^^ g' j else acc) 0 =
      Nat.rec (motive := fun _ => Nat) 0 (fun k acc => if c k then g k ^^^ acc else acc) n
  | 0, _ => rfl
  | n + 1, hg => by
    rw [List.range_succ, List.foldl_append, foldl_range_xor g g' c n fun j hj => hg j (by omega)]
    change (if c n then _ ^^^ g' n else _) = (if c n then g n ^^^ _ else _)
    rw [hg n (by omega)]
    cases c n
    · rfl
    · exact Nat.xor_comm _ _

theorem vecMulN_unpackR (d M v : Nat) : vecMulN d (unpackR d M) v = vmF d M v := by
  rw [vecMulN, vmF_rec]
  refine foldl_range_xor (rowF d M) (fun j => (unpackR d M)[j]?.getD 0) v.testBit d fun j hj => ?_
  simp [unpackR, hj, rowF_eq]

theorem mulRows_unpackR (d A B : Nat) : mulRows d (unpackR d A) (unpackR d B) = unpackR d (mulF d A B) := by
  have hA : unpackR d A = Array.ofFn fun i : Fin d => rowF d A i := by simp [unpackR, rowF_eq]
  have hv : vecMulN d (unpackR d B) = vmF d B := funext (vecMulN_unpackR d B)
  rw [mulRows, hA, Array.map_ofFn, hv, unpackR]
  congr 1
  funext i
  rw [Function.comp_apply, ← rowF_eq, mulF_eq_orN,
    rowF_orN d (fun i _ => vmF_lt d B (rowF d A i)) i.isLt]

theorem mulRows_unpackW (d A B : Nat) : mulRows d (unpackR d A) (unpackR d B) = unpackR d (mulW d A B) := by
  rw [mulW_eq, mulRows_unpackR]

theorem mul_unpackW (A B : Nat) :
    CFSG.Sporadic.Co1Schreier.Native.mul (unpackR 24 A) (unpackR 24 B) = unpackR 24 (mulW 24 A B) :=
  mulRows_unpackW 24 A B

end CFSG.KC.F2W

end
