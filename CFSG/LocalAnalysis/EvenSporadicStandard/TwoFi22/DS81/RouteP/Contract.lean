module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.FinalAll
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.LocalStatement

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSmallLie

theorem fi24Branch_of_stage44_local
    (h44 : Stage44') (hP : Fi24RecognitionLocal) : Fi24Branch := by
  intro G _ _ L h h2 hQ t ht hC
  obtain ⟨E, hEL, hM⟩ := h44 G L h h2 hQ ht hC
  refine hP G L h h2 hQ ht ?_ E hEL hM
  have ht2 : orderOf t = 2 := orderOf_eq_two_of_center h2 ht
  have htZ : t ∈ (center L).map L.subtype := ht ▸ mem_zpowers t
  have htL : t ∈ L := by
    obtain ⟨z, -, rfl⟩ := htZ
    exact z.2
  obtain ⟨htC, -, -, -, -, hLt, -⟩ := std_center_facts h.toStandardSetting ht2 htZ
  have hout := relIndex_sup_centralizer_le_two h hQ htC ht2
  obtain ⟨hCL, -⟩ := lemma44_one_two_final h h2 hQ ht
  have hLF : L ⊔ centralizer (L : Set G) = L := by
    rw [hCL]
    exact sup_eq_left.2 (zpowers_le.2 htL)
  rw [hLF] at hout
  have hne0 : L.relIndex (centralizer ({t} : Set G)) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hne1 : L.relIndex (centralizer ({t} : Set G)) ≠ 1 := fun h1 =>
    hC (le_antisymm (relIndex_eq_one.1 h1) hLt)
  omega

end CFSG.EvenSporadicStandard.TwoFi22.DS81
