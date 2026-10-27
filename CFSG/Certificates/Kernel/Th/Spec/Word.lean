
module

public import CFSG.Certificates.Kernel.Th.Spec.WordBase

public import CFSG.Certificates.Kernel.Th.Spec.Rows

public section

namespace CFSG.KC.Th.Spec

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier

section Consts

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  (K : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)

include K in
theorem wordAB_matrix_eq {A B Bi : ℕ} (w n : ℕ)
    {a b bi : Matrix (Fin 248) (Fin 248) (ZMod 2)} (hA : pkMat A = a) (hB : pkMat B = b)
    (hBi : pkMat Bi = bi) (letter : ℤ → Array V4) (ws : List ℤ)
    (hl : ∀ l ∈ ws, rowsMatrix (letter l) = codeLetter a b bi (wordCode l))
    (hcodes : ws.map wordCode = (List.range n).map fun i => bitsN w (2 * i) 2) :
    rowsMatrix (signedRows letter ws) = pkMat (wordAB c rm ONE A B Bi w n) := by
  rw [rowsMatrix_signedRows, pk_wordAB K, hA, hB, hBi]
  have e : ((List.range n).map fun i => codeLetter a b bi (bitsN w (2 * i) 2)) =
      ((List.range n).map fun i => bitsN w (2 * i) 2).map (codeLetter a b bi) := by
    rw [List.map_map]; rfl
  rw [e, ← hcodes, List.map_map]
  congr 1
  exact List.map_congr_left hl

end Consts

end CFSG.KC.Th.Spec

end
