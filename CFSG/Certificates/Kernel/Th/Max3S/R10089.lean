
module


public import CFSG.Certificates.Kernel.Th.Max3S.Words
public import CFSG.Certificates.Kernel.Th.Max3S.LeafFacts

public section

namespace CFSG.KC.Th.Max3S

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.KC.Th.Spec

theorem c10089_of (D : CFSG.KC.Th.Gen.Max3Data) (h : CFSG.KC.Th.Gen.max3Chk D = true)
    (hR : RegOK D (rowsOf (String.ofList D.ThSeed_LA)) (rowsOf (String.ofList D.ThSeed_LB))) :
    C10089 (rowsOf (String.ofList D.ThSeed_LA)) (rowsOf (String.ofList D.ThSeed_LB)) := by
  set A := rowsOf (String.ofList D.ThSeed_LA) with hAdef
  set B := rowsOf (String.ofList D.ThSeed_LB) with hBdef
  have hA : WfRows A := wfRows_rowsOf _
  have hB : WfRows B := wfRows_rowsOf _
  have hk := consts_leaf h
  have wI := wfRows_idRows
  have hONE : pkMat D.ThS_ONE = rowsMatrix idRows := by rw [pkMat_one hk, rowsMatrix_idRows]
  have lONE := inLayout_one hk
  have hmul : ∀ {P Q : ℕ} {X Y : Array V4}, pkMat P = rowsMatrix X → pkMat Q = rowsMatrix Y →
      pkMat (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm P Q) = rowsMatrix (Native.mulRows X Y) := by
    intro P Q X Y hP hQ
    rw [pkMat_mulB hk, hP, hQ, rowsMatrix_mulRows]
  have lmul : ∀ P Q : ℕ, InLayout (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm P Q) := inLayout_mulB hk
  have wx := wf_x hA hB
  have wnf := wf_nfAt hA hB
  have hconj : ∀ k : Fin 512, pkMat (conjAB D k) = rowsMatrix (conj A B k) := fun k =>
    pkMat_wordAB_encGen hk hR.x hR.y _
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_⟩
  ·
    have hc := i1Chk_true h k
    unfold i1Chk at hc
    split_ifs at hc with h0 h1 hs
    · obtain rfl : k = ⟨0, by decide⟩ := Fin.ext h0
      exact Or.inr (Or.inl (eqRows_true_of_pk (wnf _) wI (hR.nf _) hONE (eq_of_eqN hc)))
    · obtain rfl : k = ⟨1, by decide⟩ := Fin.ext h1
      exact Or.inr (Or.inr (Or.inl
        (eqRows_true_of_pk (wnf _) (wf_z hA hB) (hR.nf _) hR.z (eq_of_eqN hc))))
    · refine Or.inr (Or.inr (Or.inr ?_))
      exact eqRows_true_of_pk (wfRows_mulRows (wf_conj hA hB k) (wf_q hA hB 0))
        (wfRows_mulRows (wnf k) (wf_conj hA hB k)) (hmul (hconj k) (hR.q 0))
        (hmul (hR.nf k) (hconj k)) (eq_of_eqN hc)
    · exact Or.inl (eqRows_false_of_pk (lmul _ _) lONE (hmul (hR.nf k) (hR.nf k)) hONE
        (ne_of_neN hc))
  ·
    have hc := i2Chk_true h k
    unfold i2Chk at hc
    have hxn : pkMat (xNfB D k) = rowsMatrix (xNf A B k) := hmul hR.x (hR.nf k)
    split_ifs at hc with hs
    · refine Or.inr ?_
      exact eqRows_true_of_pk (wfRows_mulRows (wnf _) wx)
        (wfRows_mulRows (wf_xNf hA hB k) (wnf _)) (hmul (hR.nf _) hR.x)
        (hmul hxn (hR.nf _)) (eq_of_eqN hc)
    · exact Or.inl (eqRows_false_of_pk (lmul _ _) lONE (hmul hxn hxn) hONE (ne_of_neN hc))
  ·
    have hc := i3Chk_true h k
    unfold i3Chk at hc
    have hdn : pkMat (dNfB D k) = rowsMatrix (dNf A B k) := hmul hR.d (hR.nf k)
    exact eqRows_false_of_pk (lmul _ _) lONE (hmul hdn hdn) hONE (ne_of_neN hc)

end CFSG.KC.Th.Max3S

end
