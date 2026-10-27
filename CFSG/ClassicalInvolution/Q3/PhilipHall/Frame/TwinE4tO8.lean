module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4tCheck
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4O8D
public import Certificates.Certificate294002
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Check

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4O8

open CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.TL4.E4A
  CFSG.ClassicalInvolution.Q3.TL4.E4C CFSG.ClassicalInvolution.Q3.TL4.E4O8Data

theorem twinT_fin
    {sc : Equiv.Perm (Fin 360)} (hsc : IsUniqueInvolution K0 sc)
    {h : Equiv.Perm (Fin 360)} (hh : h ∈ omegaT) {t : Equiv.Perm (Fin 360)}
    (ht : IsUniqueInvolution (conjSub h K0) t) (hst : sc * t = t * sc)
    (hne : conjSub t K0 ≠ K0) :
    ∃ x ∈ omegaT, ∀ w ∈ conjSub x K0 ⊔ conjSub x (conjSub t K0),
      w * (sc * t) = (sc * t) * w := by
  have hsc2 : sc = mainPerm 0 := eq_x0_of_isUniqueInvolution hsc
  obtain ⟨k, hk, hkJ⟩ := exists_member hh
  rw [hkJ] at ht
  have htk : t = wsP.getD k 1 * sc * (wsP.getD k 1)⁻¹ := ((hsc.conj (wsP.getD k 1)).eq ht).symm
  have hchk : tCheckA 360 (L0A ()) (xA 0) (u0A ()) (v0A ()) (wsA ()) = true :=
    Certificates.certificate294002
  rw [tCheckA_eq forall₂_L0 u0_spec.1 v0_spec.1 (rep_main (by norm_num)) forall₂_ws,
    ← hsc2] at hchk
  have hrel : relevantT L0P sc u0 v0 (wsP.getD k 1 * sc * (wsP.getD k 1)⁻¹) = true := by
    rw [← htk]
    simp only [relevantT, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    refine ⟨hst.symm, ?_⟩
    rw [Bool.eq_false_iff]
    intro hn
    exact hne (conjSub_eq_of_norms mem_K0_iff hn)
  obtain ⟨l, hl, hgood⟩ := exists_good_of_tCheck hchk hk hrel
  rw [← htk] at hgood
  exact ⟨wsP.getD l 1, ws_mem l, goodWit_spec hgood⟩

end CFSG.ClassicalInvolution.Q3.TL4.E4O8
