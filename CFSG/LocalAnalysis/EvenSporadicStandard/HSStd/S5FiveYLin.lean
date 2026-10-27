module

public import CFSG.RankThree.Native.PermEnumeration

public section

namespace CFSG.EvenSporadicStandard.HSStd.FiveY

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native

@[expose] def arrCertOKL (act : ℕ → Array ℕ → Array ℕ) (ngen : ℕ) (valid : Array ℕ → Bool)
    (key : Array ℕ → ℕ) (root : Array ℕ) (c : ArrCert) : Bool :=
  decide (0 < c.pts.size) && c.pts[0]! == root &&
    (List.range c.pts.size).all (arrPointOK act ngen valid c) &&
    decide (List.IsChain (· < ·) ((c.pts.toList.map key).mergeSort (fun a b => decide (a ≤ b))))

theorem arrCertOK_of_arrCertOKL {act : ℕ → Array ℕ → Array ℕ} {ngen : ℕ}
    {valid : Array ℕ → Bool} {key : Array ℕ → ℕ} {root : Array ℕ} {c : ArrCert}
    (h : arrCertOKL act ngen valid key root c = true) :
    arrCertOK act ngen valid key root c = true := by
  simp only [arrCertOKL, arrCertOK, Bool.and_eq_true] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  have := of_decide_eq_true h2
  exact decide_eq_true (List.isChain_iff_pairwise.1 this)

@[expose] def enumOKL (n : ℕ) (gs : Array (Array ℕ)) (ps : List ℕ) (c : ArrCert) : Bool :=
  allLt gs.size (fun k => validA n gs[k]!) &&
    arrCertOKL (leftA n gs) gs.size (validA n) (keyA n ps) (idA n) c

theorem enumOK_of_enumOKL {n : ℕ} {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    (h : enumOKL n gs ps c = true) : enumOK n gs ps c = true := by
  simp only [enumOKL, enumOK, Bool.and_eq_true] at h ⊢
  exact ⟨h.1, arrCertOK_of_arrCertOKL h.2⟩

end CFSG.EvenSporadicStandard.HSStd.FiveY
