
module

public import CFSG.Certificates.Kernel.SporSch.ThColsProvedBase


public section

namespace CFSG.KS.SporSch.Pf

open CFSG.KC.Enum CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th
open Finset
open scoped Matrix

theorem par_fold (y : Nat) : ∀ l : List Nat, l.foldr (parStep y) 0 < 2 ∧
    ((l.foldr (parStep y) 0 : Nat) : ZMod 2) =
      (l.map fun j => if y.testBit j then (1 : ZMod 2) else 0).sum
  | [] => by simp
  | j :: l => by
    obtain ⟨h1, h2⟩ := par_fold y l
    rw [List.foldr_cons, List.map_cons, List.sum_cons, ← h2, parStep, bit_one]
    generalize l.foldr (parStep y) 0 = a at h1
    have ha : a = 0 ∨ a = 1 := by omega
    cases y.testBit j <;> rcases ha with rfl | rfl <;> decide

theorem par248_eq (y : Nat) : par248 y < 2 ∧ ((par248 y : Nat) : ZMod 2) =
    ∑ j ∈ range 248, if y.testBit j then (1 : ZMod 2) else 0 := by
  rw [par248, CFSG.KC.Pack.foldN_eq, ← list_sum_range]
  exact par_fold y _

end CFSG.KS.SporSch.Pf

end

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th
open CFSG.KS.SporSch.Pf
open Finset
open scoped Matrix

theorem colK_sound_proved {R : Nat → Nat} {x : Nat} (_hR : ∀ i < 248, R i < 2 ^ 248)
    (_hx : x < 2 ^ 248) :
    frApply (frTable (transposeRows (rowsV R))) (v4OfNat x) = v4OfNat (colK R x) := by
  apply V4.eq_of_toVec_eq (frApply_frTable_wf (transposeRows_wf _) _) (v4OfNat_wf (colK_lt R x))
  rw [frApply_transposeRows_toVec]
  funext i
  rw [mulVec_apply', toVec_v4OfNat, toVec_v4OfNat, rowOfNat, testBit_colK,
    decide_eq_true i.isLt, Bool.true_and]
  obtain ⟨hp, hs⟩ := par248_eq (Nat.land (R i.val) x)
  have hcast : (if Nat.beq (par248 (Nat.land (R i.val) x)) 1 = true then (1 : ZMod 2) else 0) =
      ((par248 (Nat.land (R i.val) x) : Nat) : ZMod 2) := by
    have h01 : par248 (Nat.land (R i.val) x) = 0 ∨ par248 (Nat.land (R i.val) x) = 1 := by omega
    rcases h01 with h | h <;> rw [h] <;> decide
  rw [hcast, hs, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rowsMatrix_apply, getD_rowsV R i.isLt, toVec_v4OfNat, rowOfNat]
  change _ = (if (R i.val &&& x).testBit j.val then (1 : ZMod 2) else 0)
  rw [Nat.testBit_and]
  simp only [rowOfNat]
  cases (R i.val).testBit j.val <;> cases x.testBit j.val <;> simp

end CFSG.KS.SporSch

end
