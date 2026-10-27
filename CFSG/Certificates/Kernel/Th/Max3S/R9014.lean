
module


public import CFSG.Certificates.Kernel.Th.Max3S.RegsExtra

public section

namespace CFSG.KC.Th.Max3S

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.KC.Th.Spec

private theorem pkMat_e0 {D : CFSG.KC.Th.Gen.Max3Data} {A B : Array V4} (hR : RegOK D A B) :
    pkMat (D.ThM3_RB 17) = rowsMatrix (eQ A B 0) := by
  simpa [eQ] using hR.q (0 : Fin 8)

private theorem pkMat_e1 {D : CFSG.KC.Th.Gen.Max3Data} {A B : Array V4} (hE : RegExtra D A B) :
    pkMat (D.ThM3_RB 554) = rowsMatrix (eQ A B 1) := hE.eQ1

private theorem pkMat_e2 {D : CFSG.KC.Th.Gen.Max3Data} {A B : Array V4} (hE : RegExtra D A B) :
    pkMat (D.ThM3_RB 555) = rowsMatrix (eQ A B 2) := hE.eQ2

private theorem pkMat_e3 {D : CFSG.KC.Th.Gen.Max3Data} {A B : Array V4} (hR : RegOK D A B) :
    pkMat (D.ThM3_RB 24) = rowsMatrix (eQ A B 3) := by
  simpa [eQ] using hR.q (7 : Fin 8)

private theorem pkMat_f0 {D : CFSG.KC.Th.Gen.Max3Data} {A B : Array V4} (hE : RegExtra D A B) :
    pkMat (D.ThM3_RB 556) = rowsMatrix (fQ A B 0) := hE.fQ0

private theorem pkMat_f1 {D : CFSG.KC.Th.Gen.Max3Data} {A B : Array V4} (hR : RegOK D A B) :
    pkMat (D.ThM3_RB 20) = rowsMatrix (fQ A B 1) := by
  simpa [fQ] using hR.q (3 : Fin 8)

private theorem pkMat_f2 {D : CFSG.KC.Th.Gen.Max3Data} {A B : Array V4} (hE : RegExtra D A B) :
    pkMat (D.ThM3_RB 557) = rowsMatrix (fQ A B 2) := hE.fQ2

private theorem pkMat_f3 {D : CFSG.KC.Th.Gen.Max3Data} {A B : Array V4} (hE : RegExtra D A B) :
    pkMat (D.ThM3_RB 558) = rowsMatrix (fQ A B 3) := hE.fQ3

private theorem eqRows_sq {D : CFSG.KC.Th.Gen.Max3Data} {A B : Array V4} {i : Fin 4} (P : ℕ)
    (hk : BigS.constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3
      D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE = true)
    (hP : pkMat P = rowsMatrix (eQ A B i))
    (hX : WfRows (eQ A B i)) (hONE : pkMat D.ThS_ONE = rowsMatrix idRows)
    (h : CFSG.KC.Th.mulB D.ThS_c D.ThS_rm P P = D.ThS_ONE) :
    eqRows (Native.mulRows (eQ A B i) (eQ A B i)) idRows = true := by
  refine eqRows_true_of_pk (wfRows_mulRows hX hX) wfRows_idRows ?_ hONE h
  simp only [pkMat_mulB hk, hP, rowsMatrix_mulRows]

private theorem eqRows_comm {D : CFSG.KC.Th.Gen.Max3Data} {A B : Array V4} {i j : Fin 4}
    (P Q : ℕ)
    (hk : BigS.constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3
      D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE = true)
    (hP : pkMat P = rowsMatrix (eQ A B i))
    (hQ : pkMat Q = rowsMatrix (eQ A B j))
    (hX : WfRows (eQ A B i)) (hY : WfRows (eQ A B j))
    (h : CFSG.KC.Th.mulB D.ThS_c D.ThS_rm P Q =
      CFSG.KC.Th.mulB D.ThS_c D.ThS_rm Q P) :
    eqRows (Native.mulRows (eQ A B i) (eQ A B j))
      (Native.mulRows (eQ A B j) (eQ A B i)) = true := by
  refine eqRows_true_of_pk (wfRows_mulRows hX hY) (wfRows_mulRows hY hX) ?_ ?_ h
  · simp only [pkMat_mulB hk, hP, hQ, rowsMatrix_mulRows]
  · simp only [pkMat_mulB hk, hP, hQ, rowsMatrix_mulRows]

private theorem eqRows_fz {D : CFSG.KC.Th.Gen.Max3Data} {A B : Array V4} {i : Fin 4}
    (P Q R : ℕ)
    (hk : BigS.constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3
      D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE = true)
    (hP : pkMat P = rowsMatrix (fQ A B i))
    (hQ : pkMat Q = rowsMatrix (eQ A B i))
    (hz : pkMat R = rowsMatrix (z A B))
    (hX : WfRows (fQ A B i)) (hY : WfRows (eQ A B i)) (hZ : WfRows (z A B))
    (h : CFSG.KC.Th.mulB D.ThS_c D.ThS_rm P Q =
      CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm Q R) P) :
    eqRows (Native.mulRows (fQ A B i) (eQ A B i))
      (Native.mulRows (Native.mulRows (eQ A B i) (z A B)) (fQ A B i)) = true := by
  refine eqRows_true_of_pk (wfRows_mulRows hX hY) (wfRows_mulRows (wfRows_mulRows hY hZ) hX)
    ?_ ?_ h
  · simp only [pkMat_mulB hk, hP, hQ, rowsMatrix_mulRows]
  · simp only [pkMat_mulB hk, hP, hQ, hz, rowsMatrix_mulRows]

private theorem eqRows_fcomm {D : CFSG.KC.Th.Gen.Max3Data} {A B : Array V4} {i j : Fin 4}
    (P Q : ℕ)
    (hk : BigS.constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3
      D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE = true)
    (hP : pkMat P = rowsMatrix (eQ A B i))
    (hQ : pkMat Q = rowsMatrix (fQ A B j))
    (hX : WfRows (eQ A B i)) (hY : WfRows (fQ A B j))
    (h : CFSG.KC.Th.mulB D.ThS_c D.ThS_rm Q P =
      CFSG.KC.Th.mulB D.ThS_c D.ThS_rm P Q) :
    eqRows (Native.mulRows (fQ A B j) (eQ A B i))
      (Native.mulRows (eQ A B i) (fQ A B j)) = true := by
  refine eqRows_true_of_pk (wfRows_mulRows hY hX) (wfRows_mulRows hX hY) ?_ ?_ h
  · simp only [pkMat_mulB hk, hP, hQ, rowsMatrix_mulRows]
  · simp only [pkMat_mulB hk, hP, hQ, rowsMatrix_mulRows]

private theorem c9014_sq (D : CFSG.KC.Th.Gen.Max3Data)
    (h : CFSG.KC.Th.Gen.max3Chk D = true) (A B : Array V4) (hA : WfRows A) (hB : WfRows B)
    (hR : RegOK D A B) (hE : RegExtra D A B) :
    ∀ i : Fin 4, eqRows (Native.mulRows (eQ A B i) (eQ A B i)) idRows = true := by
  have hk := consts_leaf h
  have hONE : pkMat D.ThS_ONE = rowsMatrix idRows := by rw [pkMat_one hk, rowsMatrix_idRows]
  intro i
  fin_cases i
  · exact eqRows_sq (D.ThM3_RB 17) hk (pkMat_e0 hR) (wf_eQ hA hB 0) hONE
      (eq_of_eqN (segEnd_true h 2 (by rw [segEnd_length]; decide)))
  · exact eqRows_sq (D.ThM3_RB 554) hk (pkMat_e1 hE) (wf_eQ hA hB 1) hONE
      (eq_of_eqN (segEnd_true h 3 (by rw [segEnd_length]; decide)))
  · exact eqRows_sq (D.ThM3_RB 555) hk (pkMat_e2 hE) (wf_eQ hA hB 2) hONE
      (eq_of_eqN (segEnd_true h 4 (by rw [segEnd_length]; decide)))
  · exact eqRows_sq (D.ThM3_RB 24) hk (pkMat_e3 hR) (wf_eQ hA hB 3) hONE
      (eq_of_eqN (segEnd_true h 5 (by rw [segEnd_length]; decide)))

private theorem c9014_ec0 (D : CFSG.KC.Th.Gen.Max3Data)
    (h : CFSG.KC.Th.Gen.max3Chk D = true) (A B : Array V4) (hA : WfRows A) (hB : WfRows B)
    (hR : RegOK D A B) (hE : RegExtra D A B) :
    ∀ j : Fin 4, eqRows (Native.mulRows (eQ A B 0) (eQ A B j))
      (Native.mulRows (eQ A B j) (eQ A B 0)) = true := by
  have hk := consts_leaf h
  intro j
  fin_cases j
  · exact eqRows_comm (D.ThM3_RB 17) (D.ThM3_RB 17) hk (pkMat_e0 hR) (pkMat_e0 hR)
      (wf_eQ hA hB 0) (wf_eQ hA hB 0)
      (eq_of_eqN (segEnd_true h 6 (by rw [segEnd_length]; decide)))
  · exact eqRows_comm (D.ThM3_RB 17) (D.ThM3_RB 554) hk (pkMat_e0 hR) (pkMat_e1 hE)
      (wf_eQ hA hB 0) (wf_eQ hA hB 1)
      (eq_of_eqN (segEnd_true h 7 (by rw [segEnd_length]; decide)))
  · exact eqRows_comm (D.ThM3_RB 17) (D.ThM3_RB 555) hk (pkMat_e0 hR) (pkMat_e2 hE)
      (wf_eQ hA hB 0) (wf_eQ hA hB 2)
      (eq_of_eqN (segEnd_true h 8 (by rw [segEnd_length]; decide)))
  · exact eqRows_comm (D.ThM3_RB 17) (D.ThM3_RB 24) hk (pkMat_e0 hR) (pkMat_e3 hR)
      (wf_eQ hA hB 0) (wf_eQ hA hB 3)
      (eq_of_eqN (segEnd_true h 9 (by rw [segEnd_length]; decide)))

private theorem c9014_ec1 (D : CFSG.KC.Th.Gen.Max3Data)
    (h : CFSG.KC.Th.Gen.max3Chk D = true) (A B : Array V4) (hA : WfRows A) (hB : WfRows B)
    (hR : RegOK D A B) (hE : RegExtra D A B) :
    ∀ j : Fin 4, eqRows (Native.mulRows (eQ A B 1) (eQ A B j))
      (Native.mulRows (eQ A B j) (eQ A B 1)) = true := by
  have hk := consts_leaf h
  intro j
  fin_cases j
  · exact eqRows_comm (D.ThM3_RB 554) (D.ThM3_RB 17) hk (pkMat_e1 hE) (pkMat_e0 hR)
      (wf_eQ hA hB 1) (wf_eQ hA hB 0)
      (eq_of_eqN (segEnd_true h 10 (by rw [segEnd_length]; decide)))
  · exact eqRows_comm (D.ThM3_RB 554) (D.ThM3_RB 554) hk (pkMat_e1 hE) (pkMat_e1 hE)
      (wf_eQ hA hB 1) (wf_eQ hA hB 1)
      (eq_of_eqN (segEnd_true h 11 (by rw [segEnd_length]; decide)))
  · exact eqRows_comm (D.ThM3_RB 554) (D.ThM3_RB 555) hk (pkMat_e1 hE) (pkMat_e2 hE)
      (wf_eQ hA hB 1) (wf_eQ hA hB 2)
      (eq_of_eqN (segEnd_true h 12 (by rw [segEnd_length]; decide)))
  · exact eqRows_comm (D.ThM3_RB 554) (D.ThM3_RB 24) hk (pkMat_e1 hE) (pkMat_e3 hR)
      (wf_eQ hA hB 1) (wf_eQ hA hB 3)
      (eq_of_eqN (segEnd_true h 13 (by rw [segEnd_length]; decide)))

private theorem c9014_ec2 (D : CFSG.KC.Th.Gen.Max3Data)
    (h : CFSG.KC.Th.Gen.max3Chk D = true) (A B : Array V4) (hA : WfRows A) (hB : WfRows B)
    (hR : RegOK D A B) (hE : RegExtra D A B) :
    ∀ j : Fin 4, eqRows (Native.mulRows (eQ A B 2) (eQ A B j))
      (Native.mulRows (eQ A B j) (eQ A B 2)) = true := by
  have hk := consts_leaf h
  intro j
  fin_cases j
  · exact eqRows_comm (D.ThM3_RB 555) (D.ThM3_RB 17) hk (pkMat_e2 hE) (pkMat_e0 hR)
      (wf_eQ hA hB 2) (wf_eQ hA hB 0)
      (eq_of_eqN (segEnd_true h 14 (by rw [segEnd_length]; decide)))
  · exact eqRows_comm (D.ThM3_RB 555) (D.ThM3_RB 554) hk (pkMat_e2 hE) (pkMat_e1 hE)
      (wf_eQ hA hB 2) (wf_eQ hA hB 1)
      (eq_of_eqN (segEnd_true h 15 (by rw [segEnd_length]; decide)))
  · exact eqRows_comm (D.ThM3_RB 555) (D.ThM3_RB 555) hk (pkMat_e2 hE) (pkMat_e2 hE)
      (wf_eQ hA hB 2) (wf_eQ hA hB 2)
      (eq_of_eqN (segEnd_true h 16 (by rw [segEnd_length]; decide)))
  · exact eqRows_comm (D.ThM3_RB 555) (D.ThM3_RB 24) hk (pkMat_e2 hE) (pkMat_e3 hR)
      (wf_eQ hA hB 2) (wf_eQ hA hB 3)
      (eq_of_eqN (segEnd_true h 17 (by rw [segEnd_length]; decide)))

private theorem c9014_ec3 (D : CFSG.KC.Th.Gen.Max3Data)
    (h : CFSG.KC.Th.Gen.max3Chk D = true) (A B : Array V4) (hA : WfRows A) (hB : WfRows B)
    (hR : RegOK D A B) (hE : RegExtra D A B) :
    ∀ j : Fin 4, eqRows (Native.mulRows (eQ A B 3) (eQ A B j))
      (Native.mulRows (eQ A B j) (eQ A B 3)) = true := by
  have hk := consts_leaf h
  intro j
  fin_cases j
  · exact eqRows_comm (D.ThM3_RB 24) (D.ThM3_RB 17) hk (pkMat_e3 hR) (pkMat_e0 hR)
      (wf_eQ hA hB 3) (wf_eQ hA hB 0)
      (eq_of_eqN (segEnd_true h 18 (by rw [segEnd_length]; decide)))
  · exact eqRows_comm (D.ThM3_RB 24) (D.ThM3_RB 554) hk (pkMat_e3 hR) (pkMat_e1 hE)
      (wf_eQ hA hB 3) (wf_eQ hA hB 1)
      (eq_of_eqN (segEnd_true h 19 (by rw [segEnd_length]; decide)))
  · exact eqRows_comm (D.ThM3_RB 24) (D.ThM3_RB 555) hk (pkMat_e3 hR) (pkMat_e2 hE)
      (wf_eQ hA hB 3) (wf_eQ hA hB 2)
      (eq_of_eqN (segEnd_true h 20 (by rw [segEnd_length]; decide)))
  · exact eqRows_comm (D.ThM3_RB 24) (D.ThM3_RB 24) hk (pkMat_e3 hR) (pkMat_e3 hR)
      (wf_eQ hA hB 3) (wf_eQ hA hB 3)
      (eq_of_eqN (segEnd_true h 21 (by rw [segEnd_length]; decide)))

private theorem c9014_ec (D : CFSG.KC.Th.Gen.Max3Data)
    (h : CFSG.KC.Th.Gen.max3Chk D = true) (A B : Array V4) (hA : WfRows A) (hB : WfRows B)
    (hR : RegOK D A B) (hE : RegExtra D A B) :
    ∀ i j : Fin 4, eqRows (Native.mulRows (eQ A B i) (eQ A B j))
      (Native.mulRows (eQ A B j) (eQ A B i)) = true := by
  intro i
  fin_cases i
  · exact c9014_ec0 D h A B hA hB hR hE
  · exact c9014_ec1 D h A B hA hB hR hE
  · exact c9014_ec2 D h A B hA hB hR hE
  · exact c9014_ec3 D h A B hA hB hR hE

private theorem c9014_fz (D : CFSG.KC.Th.Gen.Max3Data)
    (h : CFSG.KC.Th.Gen.max3Chk D = true) (A B : Array V4) (hA : WfRows A) (hB : WfRows B)
    (hR : RegOK D A B) (hE : RegExtra D A B) :
    ∀ i : Fin 4, eqRows (Native.mulRows (fQ A B i) (eQ A B i))
      (Native.mulRows (Native.mulRows (eQ A B i) (z A B)) (fQ A B i)) = true := by
  have hk := consts_leaf h
  intro i
  fin_cases i
  · exact eqRows_fz (D.ThM3_RB 556) (D.ThM3_RB 17) (D.ThM3_RB 16) hk
      (pkMat_f0 hE) (pkMat_e0 hR) hR.z (wf_fQ hA hB 0) (wf_eQ hA hB 0) (wf_z hA hB)
      (eq_of_eqN (segEnd_true h 22 (by rw [segEnd_length]; decide)))
  · exact eqRows_fz (D.ThM3_RB 20) (D.ThM3_RB 554) (D.ThM3_RB 16) hk
      (pkMat_f1 hR) (pkMat_e1 hE) hR.z (wf_fQ hA hB 1) (wf_eQ hA hB 1) (wf_z hA hB)
      (eq_of_eqN (segEnd_true h 23 (by rw [segEnd_length]; decide)))
  · exact eqRows_fz (D.ThM3_RB 557) (D.ThM3_RB 555) (D.ThM3_RB 16) hk
      (pkMat_f2 hE) (pkMat_e2 hE) hR.z (wf_fQ hA hB 2) (wf_eQ hA hB 2) (wf_z hA hB)
      (eq_of_eqN (segEnd_true h 24 (by rw [segEnd_length]; decide)))
  · exact eqRows_fz (D.ThM3_RB 558) (D.ThM3_RB 24) (D.ThM3_RB 16) hk
      (pkMat_f3 hE) (pkMat_e3 hR) hR.z (wf_fQ hA hB 3) (wf_eQ hA hB 3) (wf_z hA hB)
      (eq_of_eqN (segEnd_true h 25 (by rw [segEnd_length]; decide)))

private theorem c9014_fe0 (D : CFSG.KC.Th.Gen.Max3Data)
    (h : CFSG.KC.Th.Gen.max3Chk D = true) (A B : Array V4) (hA : WfRows A) (hB : WfRows B)
    (hR : RegOK D A B) (hE : RegExtra D A B) :
    ∀ i : Fin 4, i ≠ 0 → eqRows (Native.mulRows (fQ A B 0) (eQ A B i))
      (Native.mulRows (eQ A B i) (fQ A B 0)) = true := by
  have hk := consts_leaf h
  intro i hi
  fin_cases i
  · exact absurd rfl hi
  · exact eqRows_fcomm (D.ThM3_RB 554) (D.ThM3_RB 556) hk (pkMat_e1 hE) (pkMat_f0 hE)
      (wf_eQ hA hB 1) (wf_fQ hA hB 0)
      (eq_of_eqN (segEnd_true h 29 (by rw [segEnd_length]; decide)))
  · exact eqRows_fcomm (D.ThM3_RB 555) (D.ThM3_RB 556) hk (pkMat_e2 hE) (pkMat_f0 hE)
      (wf_eQ hA hB 2) (wf_fQ hA hB 0)
      (eq_of_eqN (segEnd_true h 32 (by rw [segEnd_length]; decide)))
  · exact eqRows_fcomm (D.ThM3_RB 24) (D.ThM3_RB 556) hk (pkMat_e3 hR) (pkMat_f0 hE)
      (wf_eQ hA hB 3) (wf_fQ hA hB 0)
      (eq_of_eqN (segEnd_true h 35 (by rw [segEnd_length]; decide)))

private theorem c9014_fe1 (D : CFSG.KC.Th.Gen.Max3Data)
    (h : CFSG.KC.Th.Gen.max3Chk D = true) (A B : Array V4) (hA : WfRows A) (hB : WfRows B)
    (hR : RegOK D A B) (hE : RegExtra D A B) :
    ∀ i : Fin 4, i ≠ 1 → eqRows (Native.mulRows (fQ A B 1) (eQ A B i))
      (Native.mulRows (eQ A B i) (fQ A B 1)) = true := by
  have hk := consts_leaf h
  intro i hi
  fin_cases i
  · exact eqRows_fcomm (D.ThM3_RB 17) (D.ThM3_RB 20) hk (pkMat_e0 hR) (pkMat_f1 hR)
      (wf_eQ hA hB 0) (wf_fQ hA hB 1)
      (eq_of_eqN (segEnd_true h 26 (by rw [segEnd_length]; decide)))
  · exact absurd rfl hi
  · exact eqRows_fcomm (D.ThM3_RB 555) (D.ThM3_RB 20) hk (pkMat_e2 hE) (pkMat_f1 hR)
      (wf_eQ hA hB 2) (wf_fQ hA hB 1)
      (eq_of_eqN (segEnd_true h 33 (by rw [segEnd_length]; decide)))
  · exact eqRows_fcomm (D.ThM3_RB 24) (D.ThM3_RB 20) hk (pkMat_e3 hR) (pkMat_f1 hR)
      (wf_eQ hA hB 3) (wf_fQ hA hB 1)
      (eq_of_eqN (segEnd_true h 36 (by rw [segEnd_length]; decide)))

private theorem c9014_fe2 (D : CFSG.KC.Th.Gen.Max3Data)
    (h : CFSG.KC.Th.Gen.max3Chk D = true) (A B : Array V4) (hA : WfRows A) (hB : WfRows B)
    (hR : RegOK D A B) (hE : RegExtra D A B) :
    ∀ i : Fin 4, i ≠ 2 → eqRows (Native.mulRows (fQ A B 2) (eQ A B i))
      (Native.mulRows (eQ A B i) (fQ A B 2)) = true := by
  have hk := consts_leaf h
  intro i hi
  fin_cases i
  · exact eqRows_fcomm (D.ThM3_RB 17) (D.ThM3_RB 557) hk (pkMat_e0 hR) (pkMat_f2 hE)
      (wf_eQ hA hB 0) (wf_fQ hA hB 2)
      (eq_of_eqN (segEnd_true h 27 (by rw [segEnd_length]; decide)))
  · exact eqRows_fcomm (D.ThM3_RB 554) (D.ThM3_RB 557) hk (pkMat_e1 hE) (pkMat_f2 hE)
      (wf_eQ hA hB 1) (wf_fQ hA hB 2)
      (eq_of_eqN (segEnd_true h 30 (by rw [segEnd_length]; decide)))
  · exact absurd rfl hi
  · exact eqRows_fcomm (D.ThM3_RB 24) (D.ThM3_RB 557) hk (pkMat_e3 hR) (pkMat_f2 hE)
      (wf_eQ hA hB 3) (wf_fQ hA hB 2)
      (eq_of_eqN (segEnd_true h 37 (by rw [segEnd_length]; decide)))

private theorem c9014_fe3 (D : CFSG.KC.Th.Gen.Max3Data)
    (h : CFSG.KC.Th.Gen.max3Chk D = true) (A B : Array V4) (hA : WfRows A) (hB : WfRows B)
    (hR : RegOK D A B) (hE : RegExtra D A B) :
    ∀ i : Fin 4, i ≠ 3 → eqRows (Native.mulRows (fQ A B 3) (eQ A B i))
      (Native.mulRows (eQ A B i) (fQ A B 3)) = true := by
  have hk := consts_leaf h
  intro i hi
  fin_cases i
  · exact eqRows_fcomm (D.ThM3_RB 17) (D.ThM3_RB 558) hk (pkMat_e0 hR) (pkMat_f3 hE)
      (wf_eQ hA hB 0) (wf_fQ hA hB 3)
      (eq_of_eqN (segEnd_true h 28 (by rw [segEnd_length]; decide)))
  · exact eqRows_fcomm (D.ThM3_RB 554) (D.ThM3_RB 558) hk (pkMat_e1 hE) (pkMat_f3 hE)
      (wf_eQ hA hB 1) (wf_fQ hA hB 3)
      (eq_of_eqN (segEnd_true h 31 (by rw [segEnd_length]; decide)))
  · exact eqRows_fcomm (D.ThM3_RB 555) (D.ThM3_RB 558) hk (pkMat_e2 hE) (pkMat_f3 hE)
      (wf_eQ hA hB 2) (wf_fQ hA hB 3)
      (eq_of_eqN (segEnd_true h 34 (by rw [segEnd_length]; decide)))
  · exact absurd rfl hi

private theorem c9014_fe (D : CFSG.KC.Th.Gen.Max3Data)
    (h : CFSG.KC.Th.Gen.max3Chk D = true) (A B : Array V4) (hA : WfRows A) (hB : WfRows B)
    (hR : RegOK D A B) (hE : RegExtra D A B) :
    ∀ i j : Fin 4, i ≠ j → eqRows (Native.mulRows (fQ A B j) (eQ A B i))
      (Native.mulRows (eQ A B i) (fQ A B j)) = true := by
  intro i j hij
  fin_cases j
  · exact c9014_fe0 D h A B hA hB hR hE i hij
  · exact c9014_fe1 D h A B hA hB hR hE i hij
  · exact c9014_fe2 D h A B hA hB hR hE i hij
  · exact c9014_fe3 D h A B hA hB hR hE i hij

theorem c9014_of (D : CFSG.KC.Th.Gen.Max3Data) (h : CFSG.KC.Th.Gen.max3Chk D = true)
    (hR : RegOK D (rowsOf (String.ofList D.ThSeed_LA)) (rowsOf (String.ofList D.ThSeed_LB)))
    (hE : RegExtra D (rowsOf (String.ofList D.ThSeed_LA)) (rowsOf (String.ofList D.ThSeed_LB))) :
    C9014 (rowsOf (String.ofList D.ThSeed_LA)) (rowsOf (String.ofList D.ThSeed_LB)) := by
  set A := rowsOf (String.ofList D.ThSeed_LA) with hAdef
  set B := rowsOf (String.ofList D.ThSeed_LB) with hBdef
  have hA : WfRows A := wfRows_rowsOf _
  have hB : WfRows B := wfRows_rowsOf _
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact c9014_sq D h A B hA hB hR hE
  · exact c9014_ec D h A B hA hB hR hE
  · exact c9014_fz D h A B hA hB hR hE
  · exact c9014_fe D h A B hA hB hR hE

end CFSG.KC.Th.Max3S

end
