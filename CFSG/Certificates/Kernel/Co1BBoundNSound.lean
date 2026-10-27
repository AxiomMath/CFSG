module

public import Certificates.Data.Kernel.Co1BBoundN
public import Certificates.Data.TabCo1Kit
public import CFSG.Certificates.Kernel.Co1BSpinSound

public section

namespace CFSG.KC.Co1BBoundN

open CFSG.KC.Co1BBound CFSG.KC.Co1BSpin CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.F2W CFSG.KC.M1F2 CFSG.KLie.CT
  CFSG.Sporadic.SmallF2.Native CFSG.HardMathSupport.Dickson.I271.TabCo1

theorem vecMulN_nil (x : Nat) : vecMulN 24 #[] x = 0 := by
  unfold vecMulN
  have hf : (fun acc j => if x.testBit j = true then acc ^^^ ((#[] : Array Nat)[j]?.getD 0) else acc) =
      fun acc _ => acc := by
    funext acc j
    simp
  rw [hf]
  have : ∀ (l : List Nat) (acc : Nat), l.foldl (fun acc (_ : Nat) => acc) acc = acc := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons j l ih => intro acc; exact ih acc
  exact this _ 0

theorem vm_csn {nb : Nat} {TL : List Nat} (hl : TL.length = nb) (a x : Nat) :
    vecMulN 24 (((TL.map (unpackR 24)).toArray).getD a #[]) x = vmTn nb TL a x := by
  unfold vmTn
  by_cases ha : a < nb
  · have hb : Nat.blt a nb = true := Eq.mpr Nat.blt_eq ha
    rw [hb]
    change _ = vmF 24 (getL 0 TL a) x
    have hlt : a < (TL.map (unpackR 24)).toArray.size := by simpa [hl] using ha
    rw [getL_eq, List.getElem?_eq_getElem (by omega : a < TL.length), Option.getD_some,
      Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hlt, Option.getD_some, List.getElem_toArray, List.getElem_map,
      vecMulN_unpackR]
  · have hb : Nat.blt a nb = false := by
      rw [Bool.eq_false_iff]
      intro e
      exact ha (Eq.mp Nat.blt_eq e)
    rw [hb]
    change _ = 0
    have hge : ¬ a < (TL.map (unpackR 24)).toArray.size := by simpa [hl] using ha
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none,
      vecMulN_nil]

theorem slot_eqn {nb : Nat} {TL : List Nat} (hl : TL.length = nb) (b : List Nat) (s : Nat × Nat) :
    slotN (TL.map (unpackR 24)).toArray b s = slotKn nb TL b s := by
  unfold slotN slotKn
  rw [vm_csn hl, getD_eq_getL]

theorem fN_eqn {nb : Nat} {TL : List Nat} (hl : TL.length = nb) (b : List Nat)
    (F : List (Nat × Nat)) : fN (TL.map (unpackR 24)).toArray b F = fKn nb TL b F := by
  unfold fN fKn
  simp only [slot_eqn hl]
  rfl

theorem combN_eqn {nb : Nat} {TL : List Nat} (hl : TL.length = nb) (S : List Nat) (F x : Nat) :
    combN (TL.map (unpackR 24)).toArray S F x = combKn nb TL S F x := by
  unfold combN combKn
  simp only [vm_csn hl]
  rfl

theorem slotKn_lt (nb : Nat) (TL b : List Nat) (s : Nat × Nat) : slotKn nb TL b s < 2 ^ 24 := by
  unfold slotKn vmTn
  cases Nat.blt s.2 nb
  · exact Nat.two_pow_pos 24
  · exact vmF_lt 24 _ _

end CFSG.KC.Co1BBoundN

end
