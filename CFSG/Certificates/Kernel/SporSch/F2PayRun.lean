module

public import CFSG.Certificates.Kernel.Spor.RawDefs
public import Certificates.Data.CFSGNative.J3.Basic
public import Certificates.Data.CFSGNative.HS.SmallF2
public import Certificates.Data.Kernel.SporSch.LyMat
import CFSG.Certificates.Kernel.SporSch.LyMatLemmas
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.SporSch.F2P

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.KS.Raw

theorem step_eq (D : Bool) (x idx M dd : Nat) :
    (if ((if D = true then x &&& 1 else 0) == 1 && Nat.blt idx dd) = true then M ||| 1 <<< idx
      else M) = if Nat.blt idx dd = true then M ||| ((if D = true then x else 0) % 2) <<< idx
      else M := by
  rw [Nat.and_one_is_mod]
  cases D <;> cases hb : Nat.blt idx dd <;> rcases Nat.mod_two_eq_zero_or_one x with h | h <;>
    simp [h]

theorem payRun_eqP (d : Nat) (cs : List Char) :
    ∀ ph idx M, payRun d cs ph idx M = LyM.payRunP 2 d 1 d cs ph idx M := by
  unfold payRun LyM.payRunP
  induction cs with
  | nil => intro _ _ _; rfl
  | cons ch cs ih =>
    intro ph idx M
    have ih' := funext fun ph => funext fun idx => funext fun M => ih ph idx M
    simp only
    rw [ih']
    generalize List.rec (motive := fun _ => Nat → Nat → Nat → Nat) _ _ cs = R
    simp only [Raw.Orb.strictN_eq, Raw.Orb.nIf_eq, Raw.Orb.bAnd_eq]
    split
    · rfl
    · split
      · rfl
      · congr 1
        unfold parK
        rw [Raw.Orb.nIf_eq, Raw.Orb.bAnd_eq]
        have hpos : d * (idx / d) + 1 * (idx % d) = idx := by
          rw [Nat.one_mul]
          exact Nat.div_add_mod idx d
        change _ = (if Nat.blt idx (d * d) = true then M ||| (_ % 2) <<< (d * (idx / d) + 1 * (idx % d))
          else M)
        rw [hpos]
        exact step_eq _ _ _ _ _

theorem payRun_bit (d : Nat) (cs : List Char) {i j : Nat} (hi : i < d) (hj : j < d) :
    (payRun d cs 0 0 0).testBit (d * i + j) =
      (((CFSG.Sporadic.Th.Native.decodeEntries (String.ofList cs)).toArray[i * d + j]?.getD 0) % 2
        == 1) := by
  have h := LyM.payRunP_eqL (p := 2) (d := d) (w := 1) (S := d) cs (by norm_num) (by norm_num)
    (by omega)
  have e := congrArg (fun A : Array (Array Nat) => (A[i]!)[j]!) h
  beta_reduce at e
  rw [LyM.unpackL_get hi hj] at e
  unfold CFSG.Sporadic.He.Native.rowsOf at e
  simp only at e
  rw [LyM.ofFn_get! _ hi, LyM.ofFn_get! _ hj, Nat.one_mul] at e
  have hdec : CFSG.Sporadic.He.Native.decodeEntries (String.ofList cs) =
      CFSG.Sporadic.Th.Native.decodeEntries (String.ofList cs) := rfl
  rw [hdec, ← payRun_eqP] at e
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have e' : payRun d cs 0 0 0 / 2 ^ (d * i + j) % 2 =
      (CFSG.Sporadic.Th.Native.decodeEntries (String.ofList cs)).toArray[i * d + j]?.getD 0 % 2 := by
    rw [e, Nat.pow_one]
  rw [e']
  rcases Nat.mod_two_eq_zero_or_one
    ((CFSG.Sporadic.Th.Native.decodeEntries (String.ofList cs)).toArray[i * d + j]?.getD 0) with h' | h'
  · rw [h']
    rfl
  · rw [h']
    rfl

theorem field_testBit (d M i b : Nat) :
    (pg d (mask d) M i).testBit b = (decide (b < d) && M.testBit (d * i + b)) := by
  rw [Raw.Orb.pg_eq, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm b]

theorem foldl_bits (f : Nat → Bool) (b : Nat) : ∀ m,
    ((List.range m).foldl (fun acc j => if f j then acc ||| (1 <<< j) else acc) 0).testBit b =
      (decide (b < m) && f b)
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have ih := foldl_bits f b m
    split
    · next hf =>
      rw [Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases hb : b = m
      · subst hb
        simp [hf]
      · have : (b < m + 1 ↔ b < m) := by omega
        simp [this, Ne.symm hb]
    · next hf =>
      rw [ih]
      by_cases hb : b = m
      · subst hb
        simp [hf]
      · have : (b < m + 1 ↔ b < m) := by omega
        simp [this]

theorem payRun_rowsJ3 (d : Nat) (cs : List Char) :
    CFSG.Sporadic.J3.Native.rowsOfPayload d (String.ofList cs) = unpack d d (payRun d cs 0 0 0) := by
  unfold CFSG.Sporadic.J3.Native.rowsOfPayload unpack
  refine congrArg Array.ofFn (funext fun i => Nat.eq_of_testBit_eq fun b => ?_)
  unfold CFSG.Sporadic.J3.Native.ofBits
  rw [foldl_bits, field_testBit]
  by_cases hb : b < d
  · simp only [hb, decide_true, Bool.true_and]
    rw [payRun_bit d cs i.isLt hb]
  · simp [hb]

theorem payRun_rowsHS (d : Nat) (cs : List Char) :
    CFSG.Sporadic.SmallF2.Native.rowsOfPayload d (String.ofList cs) =
      unpack d d (payRun d cs 0 0 0) := by
  unfold CFSG.Sporadic.SmallF2.Native.rowsOfPayload unpack
  refine congrArg Array.ofFn (funext fun i => Nat.eq_of_testBit_eq fun b => ?_)
  unfold CFSG.Sporadic.SmallF2.Native.ofBits
  rw [foldl_bits, field_testBit]
  by_cases hb : b < d
  · simp only [hb, decide_true, Bool.true_and]
    rw [payRun_bit d cs i.isLt hb]
  · simp [hb]

end CFSG.KS.SporSch.F2P

end
