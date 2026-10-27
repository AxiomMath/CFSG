module

public import Certificates.Data.Kernel.SporSch.PairJ3Cert
public import Certificates.Data.CFSGNative.MonsterB.Co2Data
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KS.SporSch

open CFSG.Monster.B.Co2.Native

theorem le70K_mem {cs : List Char} (h : le70K cs = true) : ∀ c ∈ cs, c.toNat ≤ 70 := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    change Bool.rec (motive := fun _ => Bool) false (le70K cs) (Nat.ble (Char.toNat c) 70) = true
      at h
    cases hb : Nat.ble (Char.toNat c) 70
    · rw [hb] at h
      exact absurd (h : false = true) Bool.false_ne_true
    · rw [hb] at h
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Nat.le_of_ble_eq_true hb
      · exact ih h x hx

theorem utf8EncodeChar_le70 {c : Char} (h : c.toNat ≤ 70) :
    String.utf8EncodeChar c = [UInt8.ofNat c.toNat] := by
  simp only [String.utf8EncodeChar]
  have h' : c.val.toNat ≤ 0x7f := by
    have : c.toNat = c.val.toNat := rfl
    omega
  simp only [h', ↓reduceIte]
  rfl

theorem bytes_le70 {cs : List Char} (h : ∀ c ∈ cs, c.toNat ≤ 70) :
    ∀ x ∈ cs.flatMap String.utf8EncodeChar, x.toNat ≤ 70 := by
  intro x hx
  obtain ⟨c, hc, hx⟩ := List.mem_flatMap.1 hx
  rw [utf8EncodeChar_le70 (h c hc), List.mem_singleton] at hx
  subst hx
  have := h c hc
  rw [UInt8.toNat_ofNat']
  omega

theorem get!_le70 {cs : List Char} (h : le70K cs = true) (i : Nat) :
    ((String.ofList cs).toUTF8.get! i).toNat ≤ 70 := by
  have hb := bytes_le70 (le70K_mem h)
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList, List.utf8Encode]
  generalize hl : cs.flatMap String.utf8EncodeChar = l at hb
  change (l.toByteArray.data[i]!).toNat ≤ 70
  rw [List.data_toByteArray, getElem!_def]
  rcases hq : l.toArray[i]? with _ | x
  · decide
  · rw [List.getElem?_toArray] at hq
    exact hb x (List.mem_of_getElem? hq)

theorem hexVal_le {x : UInt8} (h : x.toNat ≤ 70) : hexVal x ≤ 15 := by
  unfold hexVal
  split <;> omega

theorem hexAt_lt_le70 {cs : List Char} (h : le70K cs = true) (o d : Nat) :
    hexAt (String.ofList cs).toUTF8 o d < 2 ^ (4 * d) := by
  induction d with
  | zero => simp [hexAt]
  | succ w ih =>
    have hv := hexVal_le (get!_le70 h (o + w))
    rw [hexAt, show 4 * (w + 1) = 4 * w + 4 by ring, pow_add]
    omega

end CFSG.KS.SporSch
