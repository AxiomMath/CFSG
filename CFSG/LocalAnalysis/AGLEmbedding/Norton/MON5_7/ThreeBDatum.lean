module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.ThreeB
public import CFSG.HardMathSupport.Foote.E27.SporCommData
public import CFSG.Monster.B.Pinned.Primes.Data

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.Norton.MON5_7

open CFSG.Monster.B.Pinned CFSG.HardMathSupport.Foote.E27

@[expose] def tbMiRows : List (List ℕ) :=
  [[0, 1, 0, 2, 2, 2, 2, 0, 0, 0, 1, 0],
    [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1],
    [1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 2, 1],
    [1, 0, 0, 2, 0, 2, 2, 2, 2, 1, 0, 1],
    [1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 0],
    [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2],
    [0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0],
    [2, 0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0],
    [0, 0, 2, 2, 2, 0, 1, 0, 0, 0, 0, 0]]

theorem tbM_mul_inv : tbM * rowsMat 3 12 tbMiRows = 1 := by decide +kernel

theorem tbM_antisymm (i j : Fin 12) : tbM i j = - tbM j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem tbM_diag (i : Fin 12) : tbM i i = 0 := by
  fin_cases i <;> rfl

theorem tbM_val : (tbM ⟨1, by norm_num⟩ ⟨0, by norm_num⟩).val = 1 := by decide +kernel

theorem tbX_mul_inv : tbXMat * rowsMat 3 12 tbXiRows = 1 := by decide +kernel

theorem tbX_inv_mul : rowsMat 3 12 tbXiRows * tbXMat = 1 := by decide +kernel

theorem tbY_mul_inv : tbYMat * rowsMat 3 12 tbYiRows = 1 := by decide +kernel

theorem tbY_inv_mul : rowsMat 3 12 tbYiRows * tbYMat = 1 := by decide +kernel

@[expose] def tbXU : GL (Fin 12) (ZMod 3) :=
  ⟨tbXMat, rowsMat 3 12 tbXiRows, tbX_mul_inv, tbX_inv_mul⟩

@[expose] def tbYU : GL (Fin 12) (ZMod 3) :=
  ⟨tbYMat, rowsMat 3 12 tbYiRows, tbY_mul_inv, tbY_inv_mul⟩

theorem coe_tbXU : (tbXU : Matrix (Fin 12) (Fin 12) (ZMod 3)) = rowsMat 3 12 tbXRows := rfl

theorem coe_tbYU : (tbYU : Matrix (Fin 12) (Fin 12) (ZMod 3)) = rowsMat 3 12 tbYRows := rfl

theorem tbCommData : CommData 3 tbq tbw tbM :=
  commData_of_rel tbM_antisymm tbM_diag (Matrix.isUnit_det_of_right_inverse tbM_mul_inv)
    (i₀ := ⟨1, by norm_num⟩) (j₀ := ⟨0, by norm_num⟩) tbM_val tbq_pow_three
    tbw_pow_three tbw_ne_one tbq_conj_tbw tbq_chain

theorem tbb₁_conj_U (i : Fin 12) :
    tbb₁⁻¹ * tbq i * tbb₁ = (List.ofFn fun j =>
      tbq j ^ ((tbXU : Matrix (Fin 12) (Fin 12) (ZMod 3)) i j).val).prod * tbw ^ tbc₁ i :=
  tbb₁_conj i

theorem tbb₂_conj_U (i : Fin 12) :
    tbb₂⁻¹ * tbq i * tbb₂ = (List.ofFn fun j =>
      tbq j ^ ((tbYU : Matrix (Fin 12) (Fin 12) (ZMod 3)) i j).val).prod * tbw ^ tbc₂ i :=
  tbb₂_conj i

end CFSG.AGLEmbedding.Norton.MON5_7
