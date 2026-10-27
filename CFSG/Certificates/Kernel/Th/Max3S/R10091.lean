
module


public import CFSG.Certificates.Kernel.Th.Max3S.RegsExtra

public section

namespace CFSG.KC.Th.Max3S

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.KC.Th.Spec
open CFSG.ComponentClassification.PresentationLocal (CarmichaelIndex)
open CFSG.Sporadic.Th.Max3.AltQuot (carmCubeIdx carmPairIdx)

section Proofs

variable {D : CFSG.KC.Th.Gen.Max3Data} {A B : Array V4}

private lemma carmCube_eq
    (hK : BigS.constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3
      D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE = true)
    (hA : WfRows A) (hB : WfRows B) (hR : RegOK D A B) (hE : RegExtra D A B)
    (k : CarmichaelIndex 9)
    (h : CFSG.KC.Th.Gen.eqN (BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE
      (D.ThM3_RB (535 + k.1.val)) 3 2) (D.ThM3_RB (25 + (carmCubeIdx k).val)) = true) :
    eqRows (powRows (carm A B k) 3) (nfIdxRows A B (carmCubeIdx k)) = true := by
  have hn := hR.nf (carmCubeIdx k)
  rw [nfAt_eq_nfIdxRows] at hn
  refine eqRows_true_of_pk (WfRows.powRows (wf_carm hA hB k) 3)
    (wf_nfIdxRows hA hB _) ?_ hn (eq_of_eqN h)
  rw [pkMat_powB hK _ _ _ (by norm_num), hE.carm k, rowsMatrix_powRows]

private lemma carmPair_eq
    (hK : BigS.constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3
      D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE = true)
    (hA : WfRows A) (hB : WfRows B) (hR : RegOK D A B) (hE : RegExtra D A B)
    (j k : CarmichaelIndex 9)
    (h : CFSG.KC.Th.Gen.eqN (BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.mulB
      D.ThS_c D.ThS_rm (D.ThM3_RB (535 + j.1.val)) (D.ThM3_RB (535 + k.1.val))) 2 2)
      (D.ThM3_RB (25 + (carmPairIdx j k).val)) = true) :
    eqRows (powRows (Native.mulRows (carm A B j) (carm A B k)) 2)
      (nfIdxRows A B (carmPairIdx j k)) = true := by
  have hn := hR.nf (carmPairIdx j k)
  rw [nfAt_eq_nfIdxRows] at hn
  refine eqRows_true_of_pk
    (WfRows.powRows (wfRows_mulRows (wf_carm hA hB j) (wf_carm hA hB k)) 2)
    (wf_nfIdxRows hA hB _) ?_ hn (eq_of_eqN h)
  rw [pkMat_powB hK _ _ _ (by norm_num), pkMat_mulB hK, hE.carm j, hE.carm k,
    rowsMatrix_powRows, rowsMatrix_mulRows]

private lemma xwa_eq
    (hK : BigS.constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3
      D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE = true)
    (hA : WfRows A) (hB : WfRows B) (hR : RegOK D A B) (hE : RegExtra D A B)
    (h : CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 13)
      (D.ThM3_RB 544)) (D.ThM3_RB 324) = true) :
    eqRows (Native.mulRows (x A B) (wa A B)) (nfIdxRows A B 299) = true := by
  have hn := hR.nf (299 : Fin 512)
  rw [nfAt_eq_nfIdxRows] at hn
  refine eqRows_true_of_pk (wfRows_mulRows (wf_x hA hB) (wf_wa hA hB))
    (wf_nfIdxRows hA hB 299) ?_ hn (eq_of_eqN h)
  rw [pkMat_mulB hK, hR.x, hE.wa, rowsMatrix_mulRows]

private lemma y5wb_eq
    (hK : BigS.constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3
      D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE = true)
    (hA : WfRows A) (hB : WfRows B) (hR : RegOK D A B) (hE : RegExtra D A B)
    (h : CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 15)
      (D.ThM3_RB 545)) (D.ThM3_RB 226) = true) :
    eqRows (Native.mulRows (powRows (y A B) 5) (wb A B)) (nfIdxRows A B 201) = true := by
  have hn := hR.nf (201 : Fin 512)
  rw [nfAt_eq_nfIdxRows] at hn
  refine eqRows_true_of_pk
    (wfRows_mulRows (WfRows.powRows (wf_y hA hB) 5) (wf_wb hA hB))
    (wf_nfIdxRows hA hB 201) ?_ hn (eq_of_eqN h)
  rw [pkMat_mulB hK, hR.y5, hE.wb, rowsMatrix_mulRows]

end Proofs

theorem c10091_of (D : CFSG.KC.Th.Gen.Max3Data) (h : CFSG.KC.Th.Gen.max3Chk D = true)
    (hR : RegOK D (rowsOf (String.ofList D.ThSeed_LA)) (rowsOf (String.ofList D.ThSeed_LB)))
    (hE : RegExtra D (rowsOf (String.ofList D.ThSeed_LA)) (rowsOf (String.ofList D.ThSeed_LB))) :
    C10091 (rowsOf (String.ofList D.ThSeed_LA)) (rowsOf (String.ofList D.ThSeed_LB)) := by
  set A := rowsOf (String.ofList D.ThSeed_LA) with hAdef
  set B := rowsOf (String.ofList D.ThSeed_LB) with hBdef
  have hA : WfRows A := wfRows_rowsOf _
  have hB : WfRows B := wfRows_rowsOf _
  have hK := consts_leaf h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    obtain ⟨⟨k, hk9⟩, hk2⟩ := k
    interval_cases k
    · exact carmCube_eq hK hA hB hR hE _ (segMid_true h 0 (by rw [segMid_length]; decide))
    · exact carmCube_eq hK hA hB hR hE _ (segMid_true h 1 (by rw [segMid_length]; decide))
    · exact carmCube_eq hK hA hB hR hE _ (segMid_true h 2 (by rw [segMid_length]; decide))
    · exact carmCube_eq hK hA hB hR hE _ (segMid_true h 3 (by rw [segMid_length]; decide))
    · exact carmCube_eq hK hA hB hR hE _ (segMid_true h 4 (by rw [segMid_length]; decide))
    · exact carmCube_eq hK hA hB hR hE _ (segMid_true h 5 (by rw [segMid_length]; decide))
    · exact carmCube_eq hK hA hB hR hE _ (segMid_true h 6 (by rw [segMid_length]; decide))
  · intro j k hjk
    obtain ⟨⟨j, hj9⟩, hj2⟩ := j
    obtain ⟨⟨k, hk9⟩, hk2⟩ := k
    change j < k at hjk
    interval_cases j <;> interval_cases k
    · exact carmPair_eq hK hA hB hR hE _ _ (segMid_true h 7 (by rw [segMid_length]; decide))
    · exact carmPair_eq hK hA hB hR hE _ _ (segMid_true h 8 (by rw [segMid_length]; decide))
    · exact carmPair_eq hK hA hB hR hE _ _ (segMid_true h 9 (by rw [segMid_length]; decide))
    · exact carmPair_eq hK hA hB hR hE _ _ (segMid_true h 10 (by rw [segMid_length]; decide))
    · exact carmPair_eq hK hA hB hR hE _ _ (segMid_true h 11 (by rw [segMid_length]; decide))
    · exact carmPair_eq hK hA hB hR hE _ _ (segMid_true h 12 (by rw [segMid_length]; decide))
    · exact carmPair_eq hK hA hB hR hE _ _ (segMid_true h 13 (by rw [segMid_length]; decide))
    · exact carmPair_eq hK hA hB hR hE _ _ (segMid_true h 14 (by rw [segMid_length]; decide))
    · exact carmPair_eq hK hA hB hR hE _ _ (segMid_true h 15 (by rw [segMid_length]; decide))
    · exact carmPair_eq hK hA hB hR hE _ _ (segMid_true h 16 (by rw [segMid_length]; decide))
    · exact carmPair_eq hK hA hB hR hE _ _ (segMid_true h 17 (by rw [segMid_length]; decide))
    · exact carmPair_eq hK hA hB hR hE _ _ (segMid_true h 18 (by rw [segMid_length]; decide))
    · exact carmPair_eq hK hA hB hR hE _ _ (segMid_true h 19 (by rw [segMid_length]; decide))
    · exact carmPair_eq hK hA hB hR hE _ _ (segMid_true h 20 (by rw [segMid_length]; decide))
    · exact carmPair_eq hK hA hB hR hE _ _ (segMid_true h 21 (by rw [segMid_length]; decide))
    · exact carmPair_eq hK hA hB hR hE _ _ (segMid_true h 22 (by rw [segMid_length]; decide))
    · exact carmPair_eq hK hA hB hR hE _ _ (segMid_true h 23 (by rw [segMid_length]; decide))
    · exact carmPair_eq hK hA hB hR hE _ _ (segMid_true h 24 (by rw [segMid_length]; decide))
    · exact carmPair_eq hK hA hB hR hE _ _ (segMid_true h 25 (by rw [segMid_length]; decide))
    · exact carmPair_eq hK hA hB hR hE _ _ (segMid_true h 26 (by rw [segMid_length]; decide))
    · exact carmPair_eq hK hA hB hR hE _ _ (segMid_true h 27 (by rw [segMid_length]; decide))
  · exact xwa_eq hK hA hB hR hE (segMid_true h 28 (by rw [segMid_length]; decide))
  · exact y5wb_eq hK hA hB hR hE (segMid_true h 29 (by rw [segMid_length]; decide))
  · refine eqRows_false_of_pk hE.lay546 (inLayout_one hK) hE.commXQ ?_
      (ne_of_neN (segMid_true h 30 (by rw [segMid_length]; decide)))
    rw [pkMat_one hK, rowsMatrix_idRows]
  · exact eqRows_false_of_pk hE.lay546 hR.lay16 hE.commXQ hR.z
      (ne_of_neN (segMid_true h 31 (by rw [segMid_length]; decide)))

end CFSG.KC.Th.Max3S

end
