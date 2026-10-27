
module

public import CFSG.Certificates.Kernel.Th.Max3S.WordsBase

public import CFSG.Certificates.Kernel.Th.Max3S.Basic
public import CFSG.Certificates.Kernel.Th.Max3S.Leaves
public import CFSG.Sporadic.Th.BaseBase1
public import CFSG.Sporadic.Th.ChainBase1
public import CFSG.Sporadic.Th.Max3.AllConjBase1
public import CFSG.Sporadic.Th.Max3.AllConjInputs
public import CFSG.Sporadic.Th.Max3.CoreBase1
public import CFSG.Sporadic.Th.Max3.InvolutionsBase1
public import CFSG.Sporadic.Th.Max3.QuotientBase1
public import CFSG.Sporadic.Th.Max3.QuotientInputs
public import CFSG.Sporadic.ThSchreier.WordsBase1

public section

namespace CFSG.KC.Th.Max3S

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.KC.Th.Spec

section Consts

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}

theorem pkMat_wordAB_encGen
    (hk : BigS.constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true) {X Y Yi : ℕ}
    {rx ry : Array V4} (hX : pkMat X = rowsMatrix rx) (hY : pkMat Y = rowsMatrix ry)
    (w : List Gen) :
    pkMat (BigS.wordAB c rm ONE X Y Yi (encGen w) w.length) = rowsMatrix (wordRows rx ry w) := by
  rw [pkMat_wordAB_range hk, rowsMatrix_wordRows]
  congr 1
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  have hi : i < w.length := by simpa using h1
  rw [List.getElem_map, List.getElem_map, List.getElem_range, bitsN_encGen w i hi,
    wordLetter_code]
  cases w[i]
  · exact hX
  · exact hY

end Consts

end CFSG.KC.Th.Max3S

end
