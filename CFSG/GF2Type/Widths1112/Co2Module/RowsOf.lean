module

public import CFSG.Sporadic.HS.SmallF2Spec
public import Certificates.Data.CFSGNative.GF2W1112.Uniq

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Widths1112.Co2Module

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.GF2W1112

theorem w12UEqR_iff {X Y : Array ℕ} : w12UEqR X Y = true ↔ rowsMatrix 22 X = rowsMatrix 22 Y := by
  unfold w12UEqR
  rw [List.all_eq_true]
  constructor
  · intro h
    ext i j
    rw [rowsMatrix_apply, rowsMatrix_apply, toVecD_apply, toVecD_apply]
    have hi := h i.val (List.mem_range.2 i.isLt)
    rw [beq_iff_eq] at hi
    have := congrArg (fun z => z.testBit j.val) hi
    simp only [Nat.testBit_mod_two_pow, j.isLt, decide_true, Bool.true_and] at this
    rw [this]
  · intro h i hi
    rw [beq_iff_eq]
    refine Nat.eq_of_testBit_eq fun j => ?_
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hj : j < 22
    · have := congrFun (congrFun h ⟨i, List.mem_range.1 hi⟩) ⟨j, hj⟩
      rw [rowsMatrix_apply, rowsMatrix_apply, toVecD_apply, toVecD_apply] at this
      simp only [hj, decide_true, Bool.true_and]
      cases hx : (X[i]?.getD 0).testBit j <;> cases hy : (Y[i]?.getD 0).testBit j <;>
        simp_all
    · simp [hj]

end CFSG.GF2Type.Widths1112.Co2Module
