module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSplitCheck
public import Certificates.Certificate289002
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4O8D

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4O8

open CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.TL4.E4A
  CFSG.ClassicalInvolution.Q3.TL4.E4C CFSG.ClassicalInvolution.Q3.TL4.E4O8Data

theorem split_fin
    {sc : Equiv.Perm (Fin 360)} (hsc : IsUniqueInvolution K0 sc)
    {h : Equiv.Perm (Fin 360)} (hh : h ∈ omegaT) (ht : IsUniqueInvolution (conjSub h K0) sc)
    (hne : conjSub h K0 ≠ K0) :
    ∃ c ∈ omegaT, c ^ 3 = 1 ∧ conjSub c K0 = K0 ∧ (∀ y ∈ conjSub h K0, c * y = y * c) ∧
      ∃ k ∈ K0, c * k * c⁻¹ ≠ k := by
  have hsc2 : sc = mainPerm 0 := eq_x0_of_isUniqueInvolution hsc
  obtain ⟨k, hk, hkJ⟩ := exists_member hh
  rw [hkJ] at ht hne
  have hr : wsP.getD k 1 * sc * (wsP.getD k 1)⁻¹ = sc := (hsc.conj (wsP.getD k 1)).eq ht
  have hn : norms L0P u0 v0 (wsP.getD k 1) = false := by
    rw [Bool.eq_false_iff]
    intro hn
    exact hne (conjSub_eq_of_norms mem_K0_iff hn)
  have hchk : (wordsOK (splitW ()) &&
      splitCheckA 360 (L0A ()) (xA 0) (u0A ()) (v0A ()) (wsA ()) (splitA ())) = true :=
    Certificates.certificate289002
  rw [Bool.and_eq_true] at hchk
  obtain ⟨hwords, hchk⟩ := hchk
  obtain ⟨hcs, hcsmem⟩ := words_spec hwords
  have hcs' : List.Forall₂ (Rep 360) (splitA ()) (perms (splitA ())) := hcs
  have hcsmem' : ∀ g ∈ perms (splitA ()), g ∈ omegaT := hcsmem
  rw [splitCheckA_eq forall₂_L0 u0_spec.1 v0_spec.1 (rep_main (by norm_num)) forall₂_ws hcs',
    ← hsc2] at hchk
  obtain ⟨c, hc, hw⟩ := exists_split_of_check hchk hk hr hn
  obtain ⟨h3, hN, hC, hk⟩ := splitWit_spec mem_K0_iff hw
  refine ⟨c, hcsmem' c hc, h3, hN, ?_, hk⟩
  rw [hkJ]
  exact hC

end CFSG.ClassicalInvolution.Q3.TL4.E4O8
