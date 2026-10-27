
module


public import CFSG.Certificates.Kernel.Th.Spec.Base
public import CFSG.Certificates.Kernel.Th.Spec.Gj

public section

namespace CFSG.KC.Th.Spec

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.Sporadic.Th

section Consts

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE C N : Nat}

theorem eqRows_invRows_cRows
    (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (hC : SeedS.packOK C BaseS.deltaRows = true)
    (hN : Nat.beq (mulB c rm N C) ONE = true) :
    Native.eqRows (Native.mulRows (Native.invRows Native.cRows) Native.cRows) Native.idRows =
      true := by
  have hCm : pkMat C = rowsMatrix (Native.cRows ()) := by
    rw [packOK_sound hC, cRows_eq_deltaRows]
  have hNC : pkMat N * rowsMatrix (Native.cRows ()) = 1 := by
    have h := congrArg pkMat (Nat.eq_of_beq_eq_true hN)
    rw [pkMat_mulB hk, pkMat_one hk, hCm] at h
    exact h
  have hCN : rowsMatrix (Native.cRows ()) * pkMat N = 1 :=
    (mul_eq_one_comm (a := rowsMatrix (Native.cRows ())) (b := pkMat N)).2 hNC
  obtain ⟨hs, hw, -, hinv⟩ :=
    invRows_spec (Native.cRows ()) wfRows_cRows.1 wfRows_cRows.2 ⟨pkMat N, hCN⟩
  refine eqRows_of_rowsMatrix_eq (wfRows_mulRows ⟨hs, hw⟩ wfRows_cRows) wfRows_idRows ?_
  rw [rowsMatrix_mulRows, rowsMatrix_idRows]
  exact hinv

end Consts

end CFSG.KC.Th.Spec

end
