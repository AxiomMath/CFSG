
module


public import CFSG.Sporadic.Th.Certificate
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCentSoundBase1
public import CFSG.Sporadic.Th.CertificateBase1

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open scoped Matrix Pointwise

theorem rowsMatrix_seedA : rowsMatrix (rowsOf seedA) = matJ a := by
  rw [rowsMatrix_rowsOf_seedA, matJ, a_val]

theorem rowsMatrix_ab (w : List ℤ) :
    rowsMatrix (wordRows (rowsOf seedA) (rowsOf seedB) w) = matJ (wordG (pairLetters a b) w) :=
  rowsMatrix_wordRows rowsMatrix_seedA rowsMatrix_seedB a_sq_kernel b_cube_kernel w

theorem rowsMatrix_x1 :
    rowsMatrix (wordRows (rowsOf seedA) (rowsOf seedB) (abWord x1Str)) = matJ x1J := by
  rw [rowsMatrix_ab, x1J]

theorem rowsMatrix_x2 :
    rowsMatrix (wordRows (rowsOf seedA) (rowsOf seedB) (abWord x2Str)) = matJ x2J := by
  rw [rowsMatrix_ab, x2J]

theorem rowsMatrix_zRows : rowsMatrix (zRows ()) = matJ zJ := by
  rw [zRows, rowsMatrix_powRowsN, rowsMatrix_mulRows, rowsMatrix_x1, rowsMatrix_x2, zJ,
    matJ_pow, matJ_mul]

theorem rowsMatrix_xRows : rowsMatrix (xRows ()) = matJ xJ := rowsMatrix_ab xWord

theorem rowsMatrix_yRows : rowsMatrix (yRows ()) = matJ yJ := rowsMatrix_ab yWord

theorem rowsMatrix_z0Rows : rowsMatrix (z0Rows ()) = matJ z0J :=
  rowsMatrix_wordRows rowsMatrix_xRows rowsMatrix_yRows x_sq_kernel y_cube_kernel zWord0

theorem rowsMatrix_z1Rows : rowsMatrix (z1Rows ()) = matJ z1J :=
  rowsMatrix_wordRows rowsMatrix_xRows rowsMatrix_yRows x_sq_kernel y_cube_kernel zWord1

section Facts

variable {c' : ℕ} (hC : CertFacts c')
include hC

end Facts

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent
