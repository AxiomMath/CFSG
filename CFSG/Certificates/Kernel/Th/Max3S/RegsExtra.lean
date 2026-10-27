
module

public import CFSG.Certificates.Kernel.Th.Max3S.RegsExtraBase
import all CFSG.Certificates.Kernel.Th.Max3S.RegsExtraBase

public import CFSG.Certificates.Kernel.Th.Max3S.Regs

public section

namespace CFSG.KC.Th.Max3S

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.KC.Th.Spec
open CFSG.ComponentClassification.PresentationLocal (CarmichaelIndex)

section Wf

variable {A B : Array V4}

theorem wf_fusion (hA : WfRows A) {rg rgi rr : Array V4} (hg : WfRows rg) (hgi : WfRows rgi)
    (hr : WfRows rr) : WfRows (fusion A rg rgi rr) := by
  unfold fusion
  exact ((wfRows_mulRows (wfRows_mulRows (wfRows_mulRows hgi hr) hg) hA).powRows 9).mulRows hgi

theorem nfAt_eq_nfIdxRows (k : Fin 512) : nfAt A B k = nfIdxRows A B k := nfAt_eq k

theorem wf_nfIdxRows (hA : WfRows A) (hB : WfRows B) (k : Fin 512) :
    WfRows (nfIdxRows A B k) := by
  unfold nfIdxRows
  exact wf_nf hA hB _ _

theorem wf_carm (hA : WfRows A) (hB : WfRows B) (k : CarmichaelIndex 9) : WfRows (carm A B k) := by
  unfold carm
  exact wfRows_wordRows (wf_x hA hB) (wf_y hA hB) _

theorem wf_wa (hA : WfRows A) (hB : WfRows B) : WfRows (wa A B) := by
  unfold wa
  exact wfRows_mulRows (wfRows_mulRows (wfRows_mulRows (wfRows_mulRows (wfRows_mulRows
    (wfRows_mulRows (wfRows_mulRows (wfRows_mulRows (wf_carm hA hB (AltQuot.carmIdx 2))
    ((wf_carm hA hB (AltQuot.carmIdx 3)).powRows 2)) (wf_carm hA hB (AltQuot.carmIdx 2)))
    (wf_carm hA hB (AltQuot.carmIdx 4))) ((wf_carm hA hB (AltQuot.carmIdx 5)).powRows 2))
    (wf_carm hA hB (AltQuot.carmIdx 4))) (wf_carm hA hB (AltQuot.carmIdx 6)))
    ((wf_carm hA hB (AltQuot.carmIdx 7)).powRows 2)) (wf_carm hA hB (AltQuot.carmIdx 6))

theorem wf_wb (hA : WfRows A) (hB : WfRows B) : WfRows (wb A B) := by
  unfold wb
  exact wfRows_mulRows (wfRows_mulRows (wfRows_mulRows (wfRows_mulRows (wfRows_mulRows
    (wfRows_mulRows (wfRows_mulRows ((wf_carm hA hB (AltQuot.carmIdx 2)).powRows 2)
    (wf_carm hA hB (AltQuot.carmIdx 3))) ((wf_carm hA hB (AltQuot.carmIdx 4)).powRows 2))
    (wf_carm hA hB (AltQuot.carmIdx 3))) ((wf_carm hA hB (AltQuot.carmIdx 5)).powRows 2))
    (wf_carm hA hB (AltQuot.carmIdx 6))) ((wf_carm hA hB (AltQuot.carmIdx 7)).powRows 2))
    (wf_carm hA hB (AltQuot.carmIdx 8))

theorem wf_commXQ (hA : WfRows A) (hB : WfRows B) : WfRows (commXQ A B) := by
  unfold commXQ
  exact wfRows_mulRows (wfRows_mulRows (wfRows_mulRows (wf_x hA hB) (wf_q hA hB 1))
    (wf_x hA hB)) (wf_q hA hB 1)

theorem wf_ab (hA : WfRows A) (hB : WfRows B) (w : List ℕ) : WfRows (ab A B w) := by
  unfold ab
  refine wfRows_prodRows fun X hX => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hX
  unfold abLetter
  split_ifs with h
  · exact hA
  · exact hB

theorem wf_fusionQ0 (hA : WfRows A) (hB : WfRows B) : WfRows (fusionQ0 A B) := by
  unfold fusionQ0
  exact wf_fusion hA (wf_ab hA hB _) (wf_ab hA hB _) (wf_q hA hB 0)

theorem wf_fusionX (hA : WfRows A) (hB : WfRows B) : WfRows (fusionX A B) := by
  unfold fusionX
  exact wf_fusion hA (wf_ab hA hB _) (wf_ab hA hB _) (wf_x hA hB)

theorem wf_eQ (hA : WfRows A) (hB : WfRows B) (i : Fin 4) : WfRows (eQ A B i) := by
  fin_cases i
  · show WfRows (q A B 0)
    exact wf_q hA hB 0
  · show WfRows (Native.mulRows (q A B 1) (q A B 2))
    exact wfRows_mulRows (wf_q hA hB 1) (wf_q hA hB 2)
  · show WfRows (Native.mulRows (q A B 1) (q A B 5))
    exact wfRows_mulRows (wf_q hA hB 1) (wf_q hA hB 5)
  · show WfRows (q A B 7)
    exact wf_q hA hB 7

theorem wf_fQ (hA : WfRows A) (hB : WfRows B) (i : Fin 4) : WfRows (fQ A B i) := by
  fin_cases i
  · show WfRows (Native.mulRows (Native.mulRows (q A B 1) (q A B 3)) (q A B 4))
    exact wfRows_mulRows (wfRows_mulRows (wf_q hA hB 1) (wf_q hA hB 3)) (wf_q hA hB 4)
  · show WfRows (q A B 3)
    exact wf_q hA hB 3
  · show WfRows (Native.mulRows (q A B 3) (q A B 6))
    exact wfRows_mulRows (wf_q hA hB 3) (wf_q hA hB 6)
  · show WfRows (Native.mulRows (q A B 3) (q A B 4))
    exact wfRows_mulRows (wf_q hA hB 3) (wf_q hA hB 4)

end Wf

variable {D : CFSG.KC.Th.Gen.Max3Data}

structure RegExtra (D : CFSG.KC.Th.Gen.Max3Data) (A B : Array V4) : Prop where
  carm : ∀ k : CarmichaelIndex 9, pkMat (D.ThM3_RB (535 + k.1.val)) = rowsMatrix (Max3S.carm A B k)
  wa : pkMat (D.ThM3_RB 544) = rowsMatrix (Max3S.wa A B)
  wb : pkMat (D.ThM3_RB 545) = rowsMatrix (Max3S.wb A B)
  commXQ : pkMat (D.ThM3_RB 546) = rowsMatrix (Max3S.commXQ A B)
  lay546 : InLayout (D.ThM3_RB 546)
  fusionQ0 : pkMat (D.ThM3_RB 550) = rowsMatrix (Max3S.fusionQ0 A B)
  fusionX : pkMat (D.ThM3_RB 553) = rowsMatrix (Max3S.fusionX A B)
  eQ1 : pkMat (D.ThM3_RB 554) = rowsMatrix (Max3S.eQ A B 1)
  eQ2 : pkMat (D.ThM3_RB 555) = rowsMatrix (Max3S.eQ A B 2)
  fQ0 : pkMat (D.ThM3_RB 556) = rowsMatrix (Max3S.fQ A B 0)
  fQ2 : pkMat (D.ThM3_RB 557) = rowsMatrix (Max3S.fQ A B 2)
  fQ3 : pkMat (D.ThM3_RB 558) = rowsMatrix (Max3S.fQ A B 3)

private theorem pk_carm {A B : Array V4} {D : CFSG.KC.Th.Gen.Max3Data}
    (h : CFSG.KC.Th.Gen.max3Chk D = true)
    (hk : BigS.constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3
      D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE = true)
    (hx : pkMat (D.ThM3_RB 13) = rowsMatrix (x A B))
    (hy : pkMat (D.ThM3_RB 14) = rowsMatrix (y A B))
    (n : ℕ) (hn : n < 9) (h2 : 2 ≤ n) :
    pkMat (D.ThM3_RB (535 + n)) =
      rowsMatrix (wordRows (x A B) (y A B) (AltQuot.carmWord ⟨n, hn⟩)) := by
  interval_cases n
  · have hl := segPost_true h 0 (by rw [segPost_length]; decide)
    rw [show 535 + 2 = 537 by norm_num]
    rw [eq_of_eqN hl]
    exact pkMat_wordAB_encGen hk hx hy (AltQuot.carmWord 2)
  · have hl := segPost_true h 1 (by rw [segPost_length]; decide)
    rw [show 535 + 3 = 538 by norm_num]
    rw [eq_of_eqN hl]
    exact pkMat_wordAB_encGen hk hx hy (AltQuot.carmWord 3)
  · have hl := segPost_true h 2 (by rw [segPost_length]; decide)
    rw [show 535 + 4 = 539 by norm_num]
    rw [eq_of_eqN hl]
    exact pkMat_wordAB_encGen hk hx hy (AltQuot.carmWord 4)
  · have hl := segPost_true h 3 (by rw [segPost_length]; decide)
    rw [show 535 + 5 = 540 by norm_num]
    rw [eq_of_eqN hl]
    exact pkMat_wordAB_encGen hk hx hy (AltQuot.carmWord 5)
  · have hl := segPost_true h 4 (by rw [segPost_length]; decide)
    rw [show 535 + 6 = 541 by norm_num]
    rw [eq_of_eqN hl]
    exact pkMat_wordAB_encGen hk hx hy (AltQuot.carmWord 6)
  · have hl := segPost_true h 5 (by rw [segPost_length]; decide)
    rw [show 535 + 7 = 542 by norm_num]
    rw [eq_of_eqN hl]
    exact pkMat_wordAB_encGen hk hx hy (AltQuot.carmWord 7)
  · have hl := segPost_true h 6 (by rw [segPost_length]; decide)
    rw [show 535 + 8 = 543 by norm_num]
    rw [eq_of_eqN hl]
    exact pkMat_wordAB_encGen hk hx hy (AltQuot.carmWord 8)

theorem regExtra_of (D : CFSG.KC.Th.Gen.Max3Data) (h : CFSG.KC.Th.Gen.max3Chk D = true) :
    RegExtra D (rowsOf (String.ofList D.ThSeed_LA)) (rowsOf (String.ofList D.ThSeed_LB)) := by
  set A := rowsOf (String.ofList D.ThSeed_LA) with hAdef
  set B := rowsOf (String.ofList D.ThSeed_LB) with hBdef
  have hR : RegOK D A B := regOK_of D h
  have hk := consts_leaf h
  have hSA : pkMat D.ThSeed_SA = rowsMatrix A := (decOK_sound (decA_leaf h)).2
  have hSB : pkMat D.ThSeed_SB = rowsMatrix B :=
    (decOK_sound (segPre_true h 2 (by rw [segPre_length]; decide) :
      CFSG.KC.Th.SeedS.decOK D.ThSeed_SB D.ThSeed_LB = true)).2
  have hmul : ∀ {P Q : ℕ} {X Y : Array V4}, pkMat P = rowsMatrix X → pkMat Q = rowsMatrix Y →
      pkMat (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm P Q) = rowsMatrix (Native.mulRows X Y) := by
    intro P Q X Y hP hQ
    rw [pkMat_mulB hk, hP, hQ, rowsMatrix_mulRows]
  have hpow : ∀ {P : ℕ} {X : Array V4} (e nb : ℕ), e < 2 ^ nb → pkMat P = rowsMatrix X →
      pkMat (BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE P e nb) = rowsMatrix (powRows X e) := by
    intro P X e nb he hP
    rw [pkMat_powB hk _ _ _ he, hP, rowsMatrix_powRows]
  have tr : ∀ {P E : ℕ} {X : Array V4}, CFSG.KC.Th.Gen.eqN P E = true → pkMat E = rowsMatrix X →
      pkMat P = rowsMatrix X := fun hl hE => by rw [eq_of_eqN hl, hE]
  have hcarm : ∀ k : CarmichaelIndex 9,
      pkMat (D.ThM3_RB (535 + k.1.val)) = rowsMatrix (carm A B k) := by
    intro k
    exact pk_carm h hk hR.x hR.y k.1.val k.1.isLt k.2
  have hq1 : pkMat (D.ThM3_RB 18) = rowsMatrix (q A B 1) := hR.q 1
  have hwa : pkMat (D.ThM3_RB 544) = rowsMatrix (wa A B) := by
    have hl := segPost_true h 7 (by rw [segPost_length]; decide)
    unfold wa
    refine tr hl (hmul (hmul (hmul (hmul (hmul (hmul (hmul (hmul
      (hcarm (AltQuot.carmIdx 2))
      (hpow 2 2 (by norm_num) (hcarm (AltQuot.carmIdx 3))))
      (hcarm (AltQuot.carmIdx 2))) (hcarm (AltQuot.carmIdx 4)))
      (hpow 2 2 (by norm_num) (hcarm (AltQuot.carmIdx 5))))
      (hcarm (AltQuot.carmIdx 4))) (hcarm (AltQuot.carmIdx 6)))
      (hpow 2 2 (by norm_num) (hcarm (AltQuot.carmIdx 7))))
      (hcarm (AltQuot.carmIdx 6)))
  have hwb : pkMat (D.ThM3_RB 545) = rowsMatrix (wb A B) := by
    have hl := segPost_true h 8 (by rw [segPost_length]; decide)
    unfold wb
    refine tr hl (hmul (hmul (hmul (hmul (hmul (hmul (hmul
      (hpow 2 2 (by norm_num) (hcarm (AltQuot.carmIdx 2)))
      (hcarm (AltQuot.carmIdx 3))) (hpow 2 2 (by norm_num) (hcarm (AltQuot.carmIdx 4))))
      (hcarm (AltQuot.carmIdx 3))) (hpow 2 2 (by norm_num) (hcarm (AltQuot.carmIdx 5))))
      (hcarm (AltQuot.carmIdx 6))) (hpow 2 2 (by norm_num) (hcarm (AltQuot.carmIdx 7))))
      (hcarm (AltQuot.carmIdx 8)))
  have h546 : pkMat (D.ThM3_RB 546) = rowsMatrix (commXQ A B) := by
    have hl := segPost_true h 9 (by rw [segPost_length]; decide)
    unfold commXQ
    refine tr hl (hmul (hmul (hmul hR.x hq1) hR.x) hq1)
  have lay546 : InLayout (D.ThM3_RB 546) := by
    have hl := segPost_true h 9 (by rw [segPost_length]; decide)
    rw [eq_of_eqN hl]
    exact inLayout_mulB hk _ _
  have h548 : pkMat (D.ThM3_RB 548) = rowsMatrix (ab A B fusionWordQ0) := by
    have hl := segPost_true h 11 (by rw [segPost_length]; decide)
    rw [ab_eq_wordRows]
    exact tr hl (pkMat_wordAB_encGen hk hSA hSB (fusionWordQ0.map abGen))
  have h549 : pkMat (D.ThM3_RB 549) = rowsMatrix (ab A B (AllConj.invWord fusionWordQ0)) := by
    have hl := segPost_true h 12 (by rw [segPost_length]; decide)
    rw [ab_eq_wordRows]
    exact tr hl (pkMat_wordAB_encGen hk hSA hSB ((AllConj.invWord fusionWordQ0).map abGen))
  have h551 : pkMat (D.ThM3_RB 551) = rowsMatrix (ab A B fusionWordX) := by
    have hl := segPost_true h 14 (by rw [segPost_length]; decide)
    rw [ab_eq_wordRows]
    exact tr hl (pkMat_wordAB_encGen hk hSA hSB (fusionWordX.map abGen))
  have h552 : pkMat (D.ThM3_RB 552) = rowsMatrix (ab A B (AllConj.invWord fusionWordX)) := by
    have hl := segPost_true h 15 (by rw [segPost_length]; decide)
    rw [ab_eq_wordRows]
    exact tr hl (pkMat_wordAB_encGen hk hSA hSB ((AllConj.invWord fusionWordX).map abGen))
  have h550 : pkMat (D.ThM3_RB 550) = rowsMatrix (fusionQ0 A B) := by
    have hl := segPost_true h 13 (by rw [segPost_length]; decide)
    unfold fusionQ0 fusion
    exact tr hl (hmul (hpow 9 4 (by norm_num) (hmul (hmul (hmul h549 (hR.q 0)) h548) hSA)) h549)
  have h553 : pkMat (D.ThM3_RB 553) = rowsMatrix (fusionX A B) := by
    have hl := segPost_true h 16 (by rw [segPost_length]; decide)
    unfold fusionX fusion
    exact tr hl (hmul (hpow 9 4 (by norm_num) (hmul (hmul (hmul h552 hR.x) h551) hSA)) h552)
  have h554 : pkMat (D.ThM3_RB 554) = rowsMatrix (eQ A B 1) := by
    have hl := segPost_true h 17 (by rw [segPost_length]; decide)
    show pkMat (D.ThM3_RB 554) = rowsMatrix (Native.mulRows (q A B 1) (q A B 2))
    exact tr hl (hmul (hR.q 1) (hR.q 2))
  have h555 : pkMat (D.ThM3_RB 555) = rowsMatrix (eQ A B 2) := by
    have hl := segPost_true h 18 (by rw [segPost_length]; decide)
    show pkMat (D.ThM3_RB 555) = rowsMatrix (Native.mulRows (q A B 1) (q A B 5))
    exact tr hl (hmul (hR.q 1) (hR.q 5))
  have h556 : pkMat (D.ThM3_RB 556) = rowsMatrix (fQ A B 0) := by
    have hl := segPost_true h 19 (by rw [segPost_length]; decide)
    show pkMat (D.ThM3_RB 556) =
      rowsMatrix (Native.mulRows (Native.mulRows (q A B 1) (q A B 3)) (q A B 4))
    exact tr hl (hmul (hmul (hR.q 1) (hR.q 3)) (hR.q 4))
  have h557 : pkMat (D.ThM3_RB 557) = rowsMatrix (fQ A B 2) := by
    have hl := segPost_true h 20 (by rw [segPost_length]; decide)
    show pkMat (D.ThM3_RB 557) = rowsMatrix (Native.mulRows (q A B 3) (q A B 6))
    exact tr hl (hmul (hR.q 3) (hR.q 6))
  have h558 : pkMat (D.ThM3_RB 558) = rowsMatrix (fQ A B 3) := by
    have hl := segPost_true h 21 (by rw [segPost_length]; decide)
    show pkMat (D.ThM3_RB 558) = rowsMatrix (Native.mulRows (q A B 3) (q A B 4))
    exact tr hl (hmul (hR.q 3) (hR.q 4))
  exact
    { carm := hcarm
      wa := hwa
      wb := hwb
      commXQ := h546
      lay546 := lay546
      fusionQ0 := h550
      fusionX := h553
      eQ1 := h554
      eQ2 := h555
      fQ0 := h556
      fQ2 := h557
      fQ3 := h558 }

end CFSG.KC.Th.Max3S

end
