module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4tCheck
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Sp6B
public import Certificates.Certificate294001

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4Sp6

open CFSG.EvenSmallLie.Sp6 CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.TL4.E4C

theorem twinT_fin
    {sc : Equiv.Perm (Fin 36)} (hsc : IsUniqueInvolution K0 sc) {h : Equiv.Perm (Fin 36)}
    (hh : h ∈ co3X36) {t : Equiv.Perm (Fin 36)} (ht : IsUniqueInvolution (conjSub h K0) t)
    (hst : sc * t = t * sc) (hne : conjSub t K0 ≠ K0) :
    ∃ x ∈ co3X36, ∀ w ∈ conjSub x K0 ⊔ conjSub x (conjSub t K0),
      w * (sc * t) = (sc * t) * w := by
  have hsc2 : sc = sp6Rep2 := eq_rep_of_isUniqueInvolution hsc
  obtain ⟨k, hk, hkJ⟩ := exists_member hh
  rw [hkJ] at ht
  have htk : t = (ws ()).getD k 1 * sc * ((ws ()).getD k 1)⁻¹ :=
    ((hsc.conj ((ws ()).getD k 1)).eq ht).symm
  have hchk : tCheck (L0 ()) (tab sp6Rep2) (rho ()) (jay ()) (ws ()) = true :=
    Certificates.certificate294001
  rw [tab_eq, ← hsc2] at hchk
  have hrel : relevantT (L0 ()) sc (rho ()) (jay ())
      ((ws ()).getD k 1 * sc * ((ws ()).getD k 1)⁻¹) = true := by
    rw [← htk]
    simp only [relevantT, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    refine ⟨hst.symm, ?_⟩
    rw [Bool.eq_false_iff]
    intro hn
    exact hne (conjSub_eq_of_norms mem_K0_iff hn)
  obtain ⟨l, hl, hgood⟩ := exists_good_of_tCheck hchk hk hrel
  rw [← htk] at hgood
  exact ⟨(ws ()).getD l 1, ws_mem l, goodWit_spec hgood⟩

end CFSG.ClassicalInvolution.Q3.TL4.E4Sp6
