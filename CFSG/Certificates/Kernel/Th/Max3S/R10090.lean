
module


public import CFSG.Certificates.Kernel.Th.Max3S.Basic
public import CFSG.Certificates.Kernel.Th.Max3S.LeafFacts
public import CFSG.Certificates.Kernel.Th.Max3S.RegsExtraBase
public import CFSG.Certificates.Kernel.Th.Spec.Word
import CFSG.Certificates.Kernel.Th.Spec.Ts2324Base

public section

namespace CFSG.KC.Th.Max3S

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.KC.Th.Spec
  CFSG.KC.Th.BigS

section Proofs

variable {D : CFSG.KC.Th.Gen.Max3Data} {A B : Array V4}

private lemma pW_matrix_eq
    (hK : BigS.constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3
      D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE = true)
    (wx : WfRows (Mir.m3x A B)) (wy : WfRows (Mir.m3y A B))
    (hx : pkMat (D.ThM3_RB 13) = rowsMatrix (Mir.m3x A B))
    (hy : pkMat (D.ThM3_RB 14) = rowsMatrix (Mir.m3y A B))
    (hy5 : pkMat (D.ThM3_RB 15) = rowsMatrix (powRows (Mir.m3y A B) 5))
    (w : List ℤ) (code n : ℕ)
    (hl : ∀ l ∈ w, l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2)
    (hcodes : w.map wordCode = (List.range n).map fun i => bitsN code (2 * i) 2) :
    WfRows (Mir.pW A B w) ∧ rowsMatrix (Mir.pW A B w) =
      pkMat (BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14)
        (D.ThM3_RB 15) code n) := by
  refine ⟨wfRows_signedRows fun l _ => wfRows_pLet wx wy l, ?_⟩
  exact wordAB_matrix_eq hK code n rfl rfl rfl (Mir.pLet A B) w
    (fun l hl' => rowsMatrix_pLet hx.symm hy.symm hy5.symm (hl l hl')) hcodes

private lemma gen_zero_eq
    (hK : BigS.constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3
      D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE = true)
    (hq : ∀ i : Fin 8, pkMat (D.ThM3_RB (17 + i.val)) = rowsMatrix (q A B i))
    (i : Fin 8) (hs : (qPShift i).val = 0) :
    pkMat (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB (17 + i.val)) D.ThS_ONE) =
      rowsMatrix (Native.mulRows (q A B i) (powRows (z A B) (qPShift i).val)) := by
  rw [hs, pkMat_mulB hK, hq i, pkMat_one hK, rowsMatrix_mulRows, rowsMatrix_powRows,
    pow_zero, mul_one]

private lemma gen_one_eq
    (hK : BigS.constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3
      D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE = true)
    (hq : ∀ i : Fin 8, pkMat (D.ThM3_RB (17 + i.val)) = rowsMatrix (q A B i))
    (hz : pkMat (D.ThM3_RB 16) = rowsMatrix (z A B))
    (i : Fin 8) (hs : (qPShift i).val = 1) :
    pkMat (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB (17 + i.val)) (D.ThM3_RB 16)) =
      rowsMatrix (Native.mulRows (q A B i) (powRows (z A B) (qPShift i).val)) := by
  rw [hs, pkMat_mulB hK, hq i, hz, rowsMatrix_mulRows, rowsMatrix_powRows, pow_one]

end Proofs

theorem c10090_of (D : CFSG.KC.Th.Gen.Max3Data) (h : CFSG.KC.Th.Gen.max3Chk D = true)
    (hR : RegOK D (rowsOf (String.ofList D.ThSeed_LA)) (rowsOf (String.ofList D.ThSeed_LB))) :
    C10090 (rowsOf (String.ofList D.ThSeed_LA)) (rowsOf (String.ofList D.ThSeed_LB)) := by
  set A := rowsOf (String.ofList D.ThSeed_LA) with hAdef
  set B := rowsOf (String.ofList D.ThSeed_LB) with hBdef
  have hA : WfRows A := wfRows_rowsOf _
  have hB : WfRows B := wfRows_rowsOf _
  have hK := consts_leaf h
  have wx : WfRows (Mir.m3x A B) := wf_x hA hB
  have wy : WfRows (Mir.m3y A B) := wf_y hA hB
  have hx : pkMat (D.ThM3_RB 13) = rowsMatrix (Mir.m3x A B) := hR.x
  have hy : pkMat (D.ThM3_RB 14) = rowsMatrix (Mir.m3y A B) := hR.y
  have hy5 : pkMat (D.ThM3_RB 15) = rowsMatrix (powRows (Mir.m3y A B) 5) := hR.y5
  refine ⟨?_, ?_⟩
  · have hz := segMid_true h 32 (by rw [segMid_length]; decide)
    obtain ⟨wG, wM⟩ := pW_matrix_eq hK wx wy hx hy hy5 Packet.coreZWord
      1352160579797152663358438253090 52 (by decide +kernel) (by decide +kernel)
    exact eqRows_true_of_pk wG (wf_z hA hB) wM.symm hR.z (eq_of_eqN hz)
  · intro i
    fin_cases i
    · have hl := segMid_true h 33 (by rw [segMid_length]; decide)
      obtain ⟨wG, wM⟩ := pW_matrix_eq hK wx wy hx hy hy5 (Packet.coreGeneratorWords 0)
        4473924 12 (by decide +kernel) (by decide +kernel)
      exact eqRows_true_of_pk wG (wfRows_mulRows (wf_q hA hB 0) ((wf_z hA hB).powRows 0))
        wM.symm (gen_zero_eq hK hR.q 0 (by decide)) (eq_of_eqN hl)
    · have hl := segMid_true h 34 (by rw [segMid_length]; decide)
      obtain ⟨wG, wM⟩ := pW_matrix_eq hK wx wy hx hy hy5 (Packet.coreGeneratorWords 1)
        17895696 14 (by decide +kernel) (by decide +kernel)
      exact eqRows_true_of_pk wG (wfRows_mulRows (wf_q hA hB 1) ((wf_z hA hB).powRows 0))
        wM.symm (gen_zero_eq hK hR.q 1 (by decide)) (eq_of_eqN hl)
    · have hl := segMid_true h 35 (by rw [segMid_length]; decide)
      obtain ⟨wG, wM⟩ := pW_matrix_eq hK wx wy hx hy hy5 (Packet.coreGeneratorWords 2)
        85004562 14 (by decide +kernel) (by decide +kernel)
      exact eqRows_true_of_pk wG (wfRows_mulRows (wf_q hA hB 2) ((wf_z hA hB).powRows 0))
        wM.symm (gen_zero_eq hK hR.q 2 (by decide)) (eq_of_eqN hl)
    · have hl := segMid_true h 36 (by rw [segMid_length]; decide)
      obtain ⟨wG, wM⟩ := pW_matrix_eq hK wx wy hx hy hy5 (Packet.coreGeneratorWords 3)
        340018248 16 (by decide +kernel) (by decide +kernel)
      exact eqRows_true_of_pk wG (wfRows_mulRows (wf_q hA hB 3) ((wf_z hA hB).powRows 1))
        wM.symm (gen_one_eq hK hR.q hR.z 3 (by decide)) (eq_of_eqN hl)
    · have hl := segMid_true h 37 (by rw [segMid_length]; decide)
      obtain ⟨wG, wM⟩ := pW_matrix_eq hK wx wy hx hy hy5 (Packet.coreGeneratorWords 4)
        1413760074 16 (by decide +kernel) (by decide +kernel)
      exact eqRows_true_of_pk wG (wfRows_mulRows (wf_q hA hB 4) ((wf_z hA hB).powRows 0))
        wM.symm (gen_zero_eq hK hR.q 4 (by decide)) (eq_of_eqN hl)
    · have hl := segMid_true h 38 (by rw [segMid_length]; decide)
      obtain ⟨wG, wM⟩ := pW_matrix_eq hK wx wy hx hy hy5 (Packet.coreGeneratorWords 5)
        18539942178 18 (by decide +kernel) (by decide +kernel)
      exact eqRows_true_of_pk wG (wfRows_mulRows (wf_q hA hB 5) ((wf_z hA hB).powRows 0))
        wM.symm (gen_zero_eq hK hR.q 5 (by decide)) (eq_of_eqN hl)
    · have hl := segMid_true h 39 (by rw [segMid_length]; decide)
      obtain ⟨wG, wM⟩ := pW_matrix_eq hK wx wy hx hy hy5 (Packet.coreGeneratorWords 6)
        5655040296 18 (by decide +kernel) (by decide +kernel)
      exact eqRows_true_of_pk wG (wfRows_mulRows (wf_q hA hB 6) ((wf_z hA hB).powRows 0))
        wM.symm (gen_zero_eq hK hR.q 6 (by decide)) (eq_of_eqN hl)
    · have hl := segMid_true h 40 (by rw [segMid_length]; decide)
      obtain ⟨wG, wM⟩ := pW_matrix_eq hK wx wy hx hy hy5 (Packet.coreGeneratorWords 7)
        74159768712 20 (by decide +kernel) (by decide +kernel)
      exact eqRows_true_of_pk wG (wfRows_mulRows (wf_q hA hB 7) ((wf_z hA hB).powRows 1))
        wM.symm (gen_one_eq hK hR.q hR.z 7 (by decide)) (eq_of_eqN hl)

end CFSG.KC.Th.Max3S

end
