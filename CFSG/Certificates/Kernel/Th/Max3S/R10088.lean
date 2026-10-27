
module


public import CFSG.Certificates.Kernel.Th.Max3S.RegsExtra

public section

namespace CFSG.KC.Th.Max3S

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.KC.Th.Spec

theorem c10088_of (D : CFSG.KC.Th.Gen.Max3Data) (h : CFSG.KC.Th.Gen.max3Chk D = true)
    (hR : RegOK D (rowsOf (String.ofList D.ThSeed_LA)) (rowsOf (String.ofList D.ThSeed_LB)))
    (hE : RegExtra D (rowsOf (String.ofList D.ThSeed_LA)) (rowsOf (String.ofList D.ThSeed_LB))) :
    C10088 (rowsOf (String.ofList D.ThSeed_LA)) (rowsOf (String.ofList D.ThSeed_LB)) := by
  set A := rowsOf (String.ofList D.ThSeed_LA) with hAdef
  set B := rowsOf (String.ofList D.ThSeed_LB) with hBdef
  have hA : WfRows A := wfRows_rowsOf _
  have hB : WfRows B := wfRows_rowsOf _
  have hk := consts_leaf h
  have hSA : pkMat D.ThSeed_SA = rowsMatrix A := (decOK_sound (decA_leaf h)).2
  have hq0 : pkMat (D.ThM3_RB 17) = rowsMatrix (q A B 0) := hR.q 0
  refine ⟨?_, ?_⟩
  · refine eqRows_true_of_pk (wfRows_mulRows (wf_fusionQ0 hA hB) (wf_q hA hB 0))
      (wfRows_mulRows hA (wf_fusionQ0 hA hB)) ?_ ?_
      (eq_of_eqN (segEnd_true h 0 (by rw [segEnd_length]; decide)))
    · rw [pkMat_mulB hk, hE.fusionQ0, hq0, rowsMatrix_mulRows]
    · rw [pkMat_mulB hk, hSA, hE.fusionQ0, rowsMatrix_mulRows]
  · refine eqRows_true_of_pk (wfRows_mulRows (wf_fusionX hA hB) (wf_x hA hB))
      (wfRows_mulRows hA (wf_fusionX hA hB)) ?_ ?_
      (eq_of_eqN (segEnd_true h 1 (by rw [segEnd_length]; decide)))
    · rw [pkMat_mulB hk, hE.fusionX, hR.x, rowsMatrix_mulRows]
    · rw [pkMat_mulB hk, hSA, hE.fusionX, rowsMatrix_mulRows]

end CFSG.KC.Th.Max3S

end
