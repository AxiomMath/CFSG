module

public import Certificates.Data.CFSGNative.J4.Store
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KC.J4Q.VOrbStorage

open CFSG.Sporadic.J4.Native

private theorem zeros_data (n : Nat) : (zeros n).data = Array.replicate n (0 : UInt8) := by
  have loop (xs : List Nat) (b : ByteArray) :
      (xs.foldl (fun b _ => b.push 0) b).data =
        b.data ++ Array.replicate xs.length (0 : UInt8) := by
    induction xs generalizing b with
    | nil => simp
    | cons a xs ih =>
      rw [List.foldl_cons, ih]
      simp only [ByteArray.data_push, List.length_cons, Array.replicate_succ',
        Array.push_eq_append, Array.append_assoc]
  unfold zeros
  change (((forIn ([0:n] : Std.Legacy.Range) (ByteArray.emptyWithCapacity n)
    fun _ b => pure (ForInStep.yield (b.push 0))) : Id ByteArray).run).data = _
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have h := loop (List.range' 0 n 1) (ByteArray.emptyWithCapacity n)
  rw [show (ByteArray.emptyWithCapacity n).data = (#[] : Array UInt8) from rfl,
    Array.empty_append] at h
  simpa [Std.Legacy.Range.size] using h

theorem size_zeros (n : Nat) : (zeros n).size = n := by
  simpa only [ByteArray.size_data, Array.size_replicate] using
    congrArg Array.size (zeros_data n)

theorem uget_zeros (n : Nat) (i : USize) (hi : i.toNat < n) :
    (zeros n).uget i (by simpa only [size_zeros] using hi) = (0 : UInt8) := by
  change (zeros n).data[i.toNat]'(by simpa [size_zeros] using hi) = 0
  simp only [zeros_data, Array.getElem_replicate]

theorem size_wrU32 (b : ByteArray) (i x : Nat) : (wrU32 b i x).size = b.size := by
  unfold wrU32
  split
  · dsimp only
    split <;> simp only [size_uset]
  · rfl

theorem portable_slot_addresses {n i : Nat} (hn : 4 * n < 2 ^ 32) (hi : i < n) :
    i < 2 ^ 30 ∧ 4 * i + 3 < 4 * n ∧ 4 * n < 2 ^ System.Platform.numBits := by
  have hp := two_pow_numBits_ge
  omega

private theorem usize_size (b : ByteArray) (hb : b.size < 2 ^ 32) :
    b.usize.toNat = b.size := by
  simp only [ByteArray.usize, Nat.toUSize_eq, USize.toNat_ofNat']
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le hb two_pow_numBits_ge)

private theorem uget_nat (b : ByteArray) (i : USize) (h : i.toNat < b.size) :
    b.uget i h = b[i.toNat] := by
  cases b
  rfl

private theorem getElem_uset (b : ByteArray) (i : USize) (x : UInt8)
    (hi : i.toNat < b.size) (j : Nat) (hj : j < (b.uset i x hi).size) :
    (b.uset i x hi)[j]'hj =
      if i.toNat = j then x else b[j]'(by simpa only [size_uset] using hj) := by
  cases b with
  | mk bs =>
    change i.toNat < bs.size at hi
    change j < (bs.uset i x hi).size at hj
    change (bs.uset i x hi)[j]'hj =
      if i.toNat = j then x else bs[j]'(by simpa only [Array.size_uset] using hj)
    simp only [Array.uset_eq_set, Array.getElem_set]

private theorem rdU32_eq (b : ByteArray) {i : Nat}
    (hb : b.size < 2 ^ 32) (hi : 4 * i + 3 < b.size) :
    rdU32 b i =
      (((b[4 * i]'(by omega)).toUInt32 |||
          ((b[4 * i + 1]'(by omega)).toUInt32 <<< 8) |||
          ((b[4 * i + 2]'(by omega)).toUInt32 <<< 16) |||
          ((b[4 * i + 3]'hi).toUInt32 <<< 24)).toNat) := by
  have hcut : i < 2 ^ 30 := by omega
  have ho : (i.toUSize <<< (USize.ofNat 2)).toNat = 4 * i := by
    simpa [Nat.mul_comm] using toNat_shift (i := i) (s := 2) (by omega) (by omega)
  have h1 := toNat_add_small (o := i.toUSize <<< (USize.ofNat 2)) (k := 1) (by omega)
  have h2 := toNat_add_small (o := i.toUSize <<< (USize.ofNat 2)) (k := 2) (by omega)
  have h3 := toNat_add_small (o := i.toUSize <<< (USize.ofNat 2)) (k := 3) (by omega)
  have hg : (i.toUSize <<< (USize.ofNat 2)) + USize.ofNat 3 < b.usize := by
    change ((i.toUSize <<< (USize.ofNat 2)) + USize.ofNat 3).toNat < b.usize.toNat
    rw [h3, ho, usize_size b hb]
    exact hi
  simp only [rdU32, dif_pos hcut, dif_pos hg, uget_nat, ho, h1, h2, h3]

private theorem getElem_wrU32 (b : ByteArray) {i x j : Nat}
    (hb : b.size < 2 ^ 32) (hi : 4 * i + 3 < b.size) (hj : j < b.size) :
    (wrU32 b i x)[j]'(by simpa only [size_wrU32] using hj) =
      if 4 * i + 3 = j then ((UInt32.ofNat x) >>> 24).toUInt8 else
      if 4 * i + 2 = j then ((UInt32.ofNat x) >>> 16).toUInt8 else
      if 4 * i + 1 = j then ((UInt32.ofNat x) >>> 8).toUInt8 else
      if 4 * i = j then (UInt32.ofNat x).toUInt8 else b[j] := by
  have hcut : i < 2 ^ 30 := by omega
  have ho : (i.toUSize <<< (USize.ofNat 2)).toNat = 4 * i := by
    simpa [Nat.mul_comm] using toNat_shift (i := i) (s := 2) (by omega) (by omega)
  have h1 := toNat_add_small (o := i.toUSize <<< (USize.ofNat 2)) (k := 1) (by omega)
  have h2 := toNat_add_small (o := i.toUSize <<< (USize.ofNat 2)) (k := 2) (by omega)
  have h3 := toNat_add_small (o := i.toUSize <<< (USize.ofNat 2)) (k := 3) (by omega)
  have hg : (i.toUSize <<< (USize.ofNat 2)) + USize.ofNat 3 < b.usize := by
    change ((i.toUSize <<< (USize.ofNat 2)) + USize.ofNat 3).toNat < b.usize.toNat
    rw [h3, ho, usize_size b hb]
    exact hi
  simp only [wrU32, dif_pos hcut, dif_pos hg, getElem_uset, h1, h2, h3, ho]

theorem rdU32_wrU32_self (b : ByteArray) {i x : Nat}
    (hb : b.size < 2 ^ 32) (hi : 4 * i + 3 < b.size) (hx : x < 2 ^ 32) :
    rdU32 (wrU32 b i x) i = x := by
  rw [rdU32_eq _ (by simpa only [size_wrU32] using hb)
    (by simpa only [size_wrU32] using hi)]
  have h0 := getElem_wrU32 (x := x) (j := 4 * i) b hb hi (by omega)
  have h1 := getElem_wrU32 (x := x) (j := 4 * i + 1) b hb hi (by omega)
  have h2 := getElem_wrU32 (x := x) (j := 4 * i + 2) b hb hi (by omega)
  have h3 := getElem_wrU32 (x := x) (j := 4 * i + 3) b hb hi (by omega)
  simp only [show ¬4 * i + 3 = 4 * i by omega,
    show ¬4 * i + 2 = 4 * i by omega, show ¬4 * i + 1 = 4 * i by omega,
    show ¬4 * i + 3 = 4 * i + 1 by omega,
    show ¬4 * i + 2 = 4 * i + 1 by omega,
    show ¬4 * i + 3 = 4 * i + 2 by omega,
    if_false, if_pos rfl] at h0 h1 h2 h3
  simp only [ite_true] at h0 h1 h2 h3
  rw [h0, h1, h2, h3]
  have bytes (w : UInt32) :
      (w.toUInt8.toUInt32 ||| ((w >>> 8).toUInt8.toUInt32 <<< 8) |||
        ((w >>> 16).toUInt8.toUInt32 <<< 16) |||
        ((w >>> 24).toUInt8.toUInt32 <<< 24)) = w := by
    apply UInt32.toBitVec_inj.1
    simp only [UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftRight,
      UInt8.toBitVec_toUInt32, UInt32.toBitVec_toUInt8, UInt32.toBitVec_ofNat,
      BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    interval_cases k <;> simp
  rw [bytes, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hx]

theorem rdU32_wrU32_other (b : ByteArray) {i j x : Nat}
    (hb : b.size < 2 ^ 32) (hi : 4 * i + 3 < b.size)
    (hj : 4 * j + 3 < b.size) (hij : i ≠ j) :
    rdU32 (wrU32 b i x) j = rdU32 b j := by
  rw [rdU32_eq _ (by simpa only [size_wrU32] using hb)
    (by simpa only [size_wrU32] using hj), rdU32_eq b hb hj]
  have hbyte (k : Nat) (hk : k ≤ 3) :
      (wrU32 b i x)[4 * j + k]'(by rw [size_wrU32]; omega) =
        b[4 * j + k]'(by omega) := by
    rw [getElem_wrU32 b hb hi (by omega)]
    simp only [show ¬4 * i + 3 = 4 * j + k by omega,
      show ¬4 * i + 2 = 4 * j + k by omega,
      show ¬4 * i + 1 = 4 * j + k by omega,
      show ¬4 * i = 4 * j + k by omega, if_false]
  rw [show (wrU32 b i x)[4 * j]'(by rw [size_wrU32]; omega) =
      b[4 * j]'(by omega) by simpa using hbyte 0 (by omega),
    hbyte 1 (by omega), hbyte 2 (by omega), hbyte 3 (by omega)]

theorem rdU32_zeros {n i : Nat} (hn : 4 * n < 2 ^ 32) (hi : i < n) :
    rdU32 (zeros (4 * n)) i = 0 := by
  have hp := portable_slot_addresses hn hi
  rw [rdU32_eq _ (by simpa only [size_zeros] using hn)
    (by simpa only [size_zeros] using hp.2.1)]
  have hz (j : Nat) (hj : j < 4 * n) :
      (zeros (4 * n))[j]'(by simpa only [size_zeros] using hj) = 0 := by
    change (zeros (4 * n)).data[j]'(by simpa [size_zeros] using hj) = 0
    simp only [zeros_data, Array.getElem_replicate]
  rw [hz _ (by omega), hz _ (by omega), hz _ (by omega), hz _ (by omega)]
  decide

end CFSG.KC.J4Q.VOrbStorage
