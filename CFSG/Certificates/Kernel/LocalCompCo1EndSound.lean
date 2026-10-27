module

public import Certificates.Data.Kernel.Co1End
public import CFSG.Certificates.Kernel.SporSch.Co1SplitSound
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1EndTests
public import CFSG.Certificates.Kernel.SporSch.Co1MatLemmas

public section

set_option exponentiation.threshold 600

namespace CFSG.KC.Co1End

open CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block
open CFSG.ComponentClassification.RankTwoSporadic.Co1

theorem unpack_mod (X : Nat) : unpack 24 24 X = unpack 24 24 (X % 2 ^ 576) := by
  apply Array.ext
  · rw [MatL.unpack_size, MatL.unpack_size]
  · intro i h1 h2
    rw [MatL.unpack_getElem, MatL.unpack_getElem]
    have hi : i < 24 := by rwa [MatL.unpack_size] at h1
    unfold MatL.rowV
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    by_cases hj : j < 24
    · have : j + 24 * i < 576 := by omega
      simp [hj, this]
    · simp [hj]

theorem shift_mod (X : Nat) : Nat.shiftRight (X % 2 ^ 576) 576 = 0 := by
  change (X % 2 ^ 576) >>> 576 = 0
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos 576))

theorem beq_unpack (X Y : Nat) : (unpack 24 24 X == unpack 24 24 Y) = eqK X Y := by
  change _ = Nat.beq (X % 2 ^ 576) (Y % 2 ^ 576)
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, Nat.beq_eq]
  constructor
  · intro e
    rw [unpack_mod X, unpack_mod Y] at e
    exact unpack_inj (shift_mod X) (shift_mod Y) e
  · intro e
    rw [unpack_mod X, unpack_mod Y, e]

theorem validRows_unpack (X : Nat) :
    CFSG.Sporadic.Co1.InvNative.validRows (unpack 24 24 X) = true := by
  simp only [CFSG.Sporadic.Co1.InvNative.validRows, Bool.and_eq_true, beq_iff_eq,
    Array.all_eq_true, decide_eq_true_eq]
  refine ⟨MatL.unpack_size X, fun i hi => ?_⟩
  rw [MatL.unpack_getElem]
  exact (MatL.rowV_lt X i).trans_eq (by norm_num)

theorem notInR_map (x : Nat) (L : List Nat) :
    notInR (unpack 24 24 x) (L.map (unpack 24 24)) = notInK x L := by
  unfold notInR notInK
  rw [validRows_unpack, Bool.true_and, List.all_map]
  simp only [Function.comp_def, validRows_unpack, Bool.true_and, bne, beq_unpack]

theorem fourR_eq (a b : Nat) :
    fourR (unpack 24 24 a) (unpack 24 24 b) = (fourK a b).map (unpack 24 24) := by
  simp only [fourR, fourK, List.map_cons, List.map_nil, MatL.unpack_mulK, MatL.unpack_idM]

theorem commR_unpack (X Y : Nat) :
    CFSG.ComponentClassification.RankTwoSporadic.Co1.commR (unpack 24 24 X) (unpack 24 24 Y) =
      commK X Y := by
  unfold CFSG.ComponentClassification.RankTwoSporadic.Co1.commR commK
  rw [← MatL.unpack_mulK, ← MatL.unpack_mulK, beq_unpack]

theorem elemOK_eq {A X Y e c₁ c₂ a ai b bi : Nat} (db : List Nat) (hA : aR = unpack 24 24 A)
    (hX : twoBXYRows.1 = unpack 24 24 X) (hY : twoBXYRows.2 = unpack 24 24 Y)
    (ha : inv (unpack 24 24 a) = unpack 24 24 ai) (hb : inv (unpack 24 24 b) = unpack 24 24 bi) :
    co1EndElemOK (unpack 24 24 e) (unpack 24 24 c₁) (unpack 24 24 c₂) (unpack 24 24 a)
      (unpack 24 24 b) db = elemK A X Y e c₁ c₂ a ai b bi db := by
  unfold co1EndElemOK co1EndSwapOK co1EndConjOK conjR co1E2R elemK swapK conjOKK
  rw [hA, hX, hY, ha, hb]
  simp only [← MatL.unpack_mulK, ← MatL.unpack_idM, ← unpack_powK, beq_unpack, commR_unpack,
    fourR_eq, List.getD_map, notInR_map]
  have h1 : [unpack 24 24 idM] = [idM].map (unpack 24 24) := rfl
  have h2 : [unpack 24 24 idM, unpack 24 24 A] = [idM, A].map (unpack 24 24) := rfl
  rw [h1, h2, notInR_map, notInR_map]

end CFSG.KC.Co1End

end
