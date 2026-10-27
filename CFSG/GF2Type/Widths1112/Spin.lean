module

public import CFSG.Sporadic.HS.SmallF2Spec
public import Certificates.Data.CFSGNative.GF2W1112.Spin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.GF2W1112 CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

namespace CFSG.GF2Type.Widths1112

private theorem foldl_dot_zmod' (x y : ℕ) (m : ℕ) (init : Bool) :
    (if (List.range m).foldl (fun acc j => acc ^^ (x.testBit j && y.testBit j)) init = true
        then (1 : ZMod 2) else 0) =
      (if init = true then 1 else 0) +
        ∑ j ∈ Finset.range m,
          (if (x.testBit j && y.testBit j) = true then (1 : ZMod 2) else 0) := by
  induction m with
  | zero => cases init <;> simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ, ← add_assoc, ← ih]
    generalize (List.range m).foldl (fun acc j => acc ^^ (x.testBit j && y.testBit j)) init = b
    cases b <;> cases x.testBit m <;> cases y.testBit m <;> decide

theorem toVecD_dotProduct_w12 (d x y : ℕ) :
    toVecD d x ⬝ᵥ toVecD d y = if w12Dot d x y = true then 1 else 0 := by
  unfold w12Dot
  rw [foldl_dot_zmod']
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
  rw [dotProduct, ← Fin.sum_univ_eq_sum_range
      (fun j => if (x.testBit j && y.testBit j) = true then (1 : ZMod 2) else 0) d]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toVecD_apply, toVecD_apply]
  cases x.testBit j.val <;> cases y.testBit j.val <;> simp

theorem w12QN_spec (d : ℕ) (Qm : Array ℕ) (x : ℕ) :
    toVecD d x ⬝ᵥ (rowsMatrix d Qm *ᵥ toVecD d x) =
      if w12QN d (transposeRows d Qm) x = true then 1 else 0 := by
  rw [rowsMatrix_mulVec, toVecD_dotProduct_w12]
  rfl

theorem w12BN_spec (d : ℕ) (Fm : Array ℕ) (x y : ℕ) :
    toVecD d x ⬝ᵥ (rowsMatrix d Fm *ᵥ toVecD d y) =
      if w12BN d (transposeRows d Fm) x y = true then 1 else 0 := by
  rw [rowsMatrix_mulVec, toVecD_dotProduct_w12]
  rfl

end CFSG.GF2Type.Widths1112
