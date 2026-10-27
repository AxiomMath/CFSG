module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.SubgroupLists.DicksonGL2

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.P812

open CFSG.RankThree.SubgroupLists
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ev (i : Fin 3) : Fin 3 → ZMod 3 := Pi.single i 1

@[expose] def cline (i : Fin 3) : Submodule (ZMod 3) (Fin 3 → ZMod 3) :=
  Submodule.span (ZMod 3) {ev i}

@[expose] def cplane (i : Fin 3) : Submodule (ZMod 3) (Fin 3 → ZMod 3) :=
  Submodule.span (ZMod 3) {v | ∃ j, j ≠ i ∧ v = ev j}

@[expose] def dA : GL (Fin 3) (ZMod 3) where
  val := Matrix.diagonal ![1, -1, 1]
  inv := Matrix.diagonal ![1, -1, 1]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply] <;> decide
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply] <;> decide

@[expose] def dB : GL (Fin 3) (ZMod 3) where
  val := Matrix.diagonal ![1, 1, -1]
  inv := Matrix.diagonal ![1, 1, -1]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply] <;> decide
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply] <;> decide

@[expose] def xiK (k : Fin 3) (hk : k ≠ 0) : GL (Fin 3) (ZMod 3) :=
  Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hk (1 : ZMod 3))

theorem dA_mulVec (v : Fin 3 → ZMod 3) :
    ((dA : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = ![v 0, -v 1, v 2] := by
  ext i
  fin_cases i <;> simp [dA, Matrix.mulVec_diagonal]

theorem dB_mulVec (v : Fin 3 → ZMod 3) :
    ((dB : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = ![v 0, v 1, -v 2] := by
  ext i
  fin_cases i <;> simp [dB, Matrix.mulVec_diagonal]

theorem xiK_val (k : Fin 3) (hk : k ≠ 0) :
    ((xiK k hk : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
      1 + Matrix.single k 0 (1 : ZMod 3) :=
  rfl

theorem xiK_mulVec (k : Fin 3) (hk : k ≠ 0) (v : Fin 3 → ZMod 3) :
    ((xiK k hk : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v =
      v + v 0 • ev k := by
  rw [xiK_val, Matrix.add_mulVec, Matrix.one_mulVec]
  congr 1
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.single_apply, ev, Pi.single_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases k <;> simp_all

end CFSG.LocalAnalysis.RankThreeUC.S15.P812
