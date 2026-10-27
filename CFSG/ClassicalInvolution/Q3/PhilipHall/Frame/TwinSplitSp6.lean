module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSplitCheck
public import Certificates.Certificate289001
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Sp6B

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4Sp6

open CFSG.EvenSmallLie.Sp6 CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.TL4.E4C

theorem split_fin
    {sc : Equiv.Perm (Fin 36)} (hsc : IsUniqueInvolution K0 sc) {h : Equiv.Perm (Fin 36)}
    (hh : h ∈ co3X36) (ht : IsUniqueInvolution (conjSub h K0) sc) (hne : conjSub h K0 ≠ K0) :
    ∃ c ∈ co3X36, c ^ 3 = 1 ∧ conjSub c K0 = K0 ∧ (∀ y ∈ conjSub h K0, c * y = y * c) ∧
      ∃ k ∈ K0, c * k * c⁻¹ ≠ k := by
  have hsc2 : sc = sp6Rep2 := eq_rep_of_isUniqueInvolution hsc
  obtain ⟨k, hk, hkJ⟩ := exists_member hh
  rw [hkJ] at ht hne
  have hr : (ws ()).getD k 1 * sc * ((ws ()).getD k 1)⁻¹ = sc :=
    (hsc.conj ((ws ()).getD k 1)).eq ht
  have hn : norms (L0 ()) (rho ()) (jay ()) ((ws ()).getD k 1) = false := by
    rw [Bool.eq_false_iff]
    intro hn
    exact hne (conjSub_eq_of_norms mem_K0_iff hn)
  have hchk : splitCheck (L0 ()) (tab sp6Rep2) (rho ()) (jay ()) (ws ()) [splitWit ()] = true :=
    Certificates.certificate289001
  rw [tab_eq, ← hsc2] at hchk
  obtain ⟨c, hc, hw⟩ := exists_split_of_check hchk hk hr hn
  rw [List.mem_singleton] at hc
  subst hc
  obtain ⟨h3, hN, hC, hk⟩ := splitWit_spec mem_K0_iff hw
  refine ⟨splitWit (), ?_, h3, hN, ?_, hk⟩
  · rw [splitWit, tab_eq, ← sp6Q_originalSubgroup]
    exact evalCodes_mem _ sp6Gens_mem splitWord
  · rw [hkJ]
    exact hC

end CFSG.ClassicalInvolution.Q3.TL4.E4Sp6
