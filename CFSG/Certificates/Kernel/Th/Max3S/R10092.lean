
module

public import CFSG.Certificates.Kernel.Th.Max3S.R10092Base

public import CFSG.Certificates.Kernel.Th.Max3S.Basic
public import CFSG.Certificates.Kernel.Th.Max3S.LeafFacts

public section

namespace CFSG.KC.Th.Max3S

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.KC.Th.Spec

theorem nfAt_nfIdx {A B : Array V4} {s : ℕ} {e : Fin 8 → ℕ} (hs : s < 2) (he : ∀ j, e j < 2) :
    nfAt A B ⟨nfIdx s e, nfIdx_lt hs he⟩ = nf A B s e := by
  rw [nfAt_eq]
  have h0 := he 0; have h1 := he 1; have h2 := he 2; have h3 := he 3; have h4 := he 4
  have h5 := he 5; have h6 := he 6; have h7 := he 7
  congr 1
  · show nfIdx s e % 2 = s
    unfold nfIdx; omega
  · funext j
    show nfIdx s e / 2 ^ (j.val + 1) % 2 = e j
    unfold nfIdx
    fin_cases j <;> simp <;> omega

theorem pkMat_zPow {D : CFSG.KC.Th.Gen.Max3Data} {A B : Array V4}
    (hk : BigS.constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4
      D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE = true)
    (hz : pkMat (D.ThM3_RB 16) = rowsMatrix (z A B)) (i j : Fin 8) :
    pkMat (zPow D i j) = rowsMatrix (powRows (z A B) (c i j).val) := by
  unfold zPow
  split_ifs with hc
  · rw [hc, pkMat_one hk, powRows, rowsMatrix_idRows]
  · have h1 : (c i j).val = 1 := by have := ZMod.val_lt (c i j); omega
    rw [h1, pkMat_powB hk _ _ _ (by norm_num), hz, powRows, pow_one]

theorem c10092_of (D : CFSG.KC.Th.Gen.Max3Data) (h : CFSG.KC.Th.Gen.max3Chk D = true)
    (hR : RegOK D (rowsOf (String.ofList D.ThSeed_LA)) (rowsOf (String.ofList D.ThSeed_LB))) :
    C10092 (rowsOf (String.ofList D.ThSeed_LA)) (rowsOf (String.ofList D.ThSeed_LB)) := by
  set A := rowsOf (String.ofList D.ThSeed_LA) with hAdef
  set B := rowsOf (String.ofList D.ThSeed_LB) with hBdef
  have hA : WfRows A := wfRows_rowsOf _
  have hB : WfRows B := wfRows_rowsOf _
  have hk := consts_leaf h
  have hSA : pkMat D.ThSeed_SA = rowsMatrix A := (decOK_sound (decA_leaf h)).2
  have wI := wfRows_idRows
  have hONE : pkMat D.ThS_ONE = rowsMatrix idRows := by rw [pkMat_one hk, rowsMatrix_idRows]
  have hmul : ∀ {P Q : ℕ} {X Y : Array V4}, pkMat P = rowsMatrix X → pkMat Q = rowsMatrix Y →
      pkMat (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm P Q) = rowsMatrix (Native.mulRows X Y) := by
    intro P Q X Y hP hQ
    rw [pkMat_mulB hk, hP, hQ, rowsMatrix_mulRows]
  have hpow : ∀ {P : ℕ} {X : Array V4} (e nb : ℕ), e < 2 ^ nb → pkMat P = rowsMatrix X →
      pkMat (BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE P e nb) = rowsMatrix (powRows X e) := by
    intro P X e nb he hP
    rw [pkMat_powB hk _ _ _ he, hP, rowsMatrix_powRows]
  have wx := wf_x hA hB
  have wy := wf_y hA hB
  have wz := wf_z hA hB
  have wq := wf_q hA hB
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact eqRows_true_of_pk (WfRows.powRows (wf_t8 hA hB) 3) wI
      (hpow 3 2 (by norm_num) hR.t8) hONE (eq_of_eqN (t8_leaf h))
  · exact eqRows_true_of_pk (WfRows.powRows (wf_s8' hA hB) 19) wI
      (hpow 19 5 (by norm_num) hR.s8') hONE (eq_of_eqN (s8_leaf h))
  · exact eqRows_true_of_pk (wfRows_mulRows wx wx) wI (hmul hR.x hR.x) hONE
      (eq_of_eqN (xx_leaf h))
  · exact eqRows_true_of_pk (WfRows.powRows wy 6) wI (hpow 6 3 (by norm_num) hR.y) hONE
      (eq_of_eqN (y6_leaf h))
  · exact eqRows_true_of_pk wz hA hR.z hSA (eq_of_eqN (za_leaf h))
  · exact eqRows_false_of_pk hR.lay16 (inLayout_one hk) hR.z hONE (ne_of_neN (z1_leaf h))
  · exact eqRows_true_of_pk (wfRows_mulRows wz wz) wI (hmul hR.z hR.z) hONE
      (eq_of_eqN (zz_leaf h))
  · exact eqRows_true_of_pk (wfRows_mulRows wz wx) (wfRows_mulRows wx wz) (hmul hR.z hR.x)
      (hmul hR.x hR.z) (eq_of_eqN (zx_leaf h))
  · exact eqRows_true_of_pk (wfRows_mulRows wz wy) (wfRows_mulRows wy wz) (hmul hR.z hR.y)
      (hmul hR.y hR.z) (eq_of_eqN (zy_leaf h))
  · intro i
    exact eqRows_true_of_pk (wfRows_mulRows (wq i) (wq i)) wI (hmul (hR.q i) (hR.q i)) hONE
      (eq_of_eqN (qqChk_true h i))
  · intro i
    exact eqRows_true_of_pk (wfRows_mulRows wz (wq i)) (wfRows_mulRows (wq i) wz)
      (hmul hR.z (hR.q i)) (hmul (hR.q i) hR.z) (eq_of_eqN (zqChk_true h i))
  · intro i j
    exact eqRows_true_of_pk (wfRows_mulRows (wq i) (wq j))
      (wfRows_mulRows (wfRows_mulRows (wq j) (wq i)) (WfRows.powRows wz _))
      (hmul (hR.q i) (hR.q j)) (hmul (hmul (hR.q j) (hR.q i)) (pkMat_zPow hk hR.z i j))
      (eq_of_eqN (qcChk_true h i j))
  · intro i
    have hs : (xz i).val < 2 := ZMod.val_lt _
    have he : ∀ j, (xv i j).val < 2 := fun j => ZMod.val_lt _
    have hn := hR.nf ⟨_, nfIdx_lt hs he⟩
    rw [nfAt_nfIdx hs he] at hn
    exact eqRows_true_of_pk (wfRows_mulRows (wfRows_mulRows wx (wq i)) wx) (wf_nf hA hB _ _)
      (hmul (hmul hR.x (hR.q i)) hR.x) hn (eq_of_eqN (xqChk_true h i))
  · intro i
    have hs : (yz i).val < 2 := ZMod.val_lt _
    have he : ∀ j, (yv i j).val < 2 := fun j => ZMod.val_lt _
    have hn := hR.nf ⟨_, nfIdx_lt hs he⟩
    rw [nfAt_nfIdx hs he] at hn
    exact eqRows_true_of_pk (wfRows_mulRows (wfRows_mulRows wy (wq i)) (WfRows.powRows wy 5))
      (wf_nf hA hB _ _) (hmul (hmul hR.y (hR.q i)) hR.y5) hn (eq_of_eqN (yqChk_true h i))
  ·
    intro k l hlk
    let f : ℕ → ℕ := fun a => D.ThM3_RB (25 + a)
    have hchain : List.IsChain (fun a b => f a < f b) ndChain := ndChain_chain h
    haveI : Trans (fun a b => f a < f b) (fun a b => f a < f b) (fun a b => f a < f b) :=
      ⟨fun h1 h2 => lt_trans h1 h2⟩
    have hpw : ndChain.Pairwise (fun a b => f a ≠ f b) :=
      (List.isChain_iff_pairwise.1 hchain).imp fun h => ne_of_lt h
    haveI : Std.Symm (fun a b => f a ≠ f b) := ⟨fun _ _ h => Ne.symm h⟩
    have hmem : ∀ k : Fin 512, k.val ∈ ndChain := by decide +kernel
    have hkl : k.val ≠ l.val := fun e => absurd hlk (by rw [Fin.lt_def, e]; exact lt_irrefl _)
    exact eqRows_false_of_pk (hR.layNf k) (hR.layNf l) (hR.nf k) (hR.nf l)
      (hpw.forall (hmem k) (hmem l) hkl)

end CFSG.KC.Th.Max3S

end
