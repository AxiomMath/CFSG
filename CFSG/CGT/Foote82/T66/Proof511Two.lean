module

public import CFSG.CGT.Foote82.T66.CitedCaseII
public import CFSG.CGT.Foote82.T66.Proof511One
public import CFSG.CGT.Foote82.T66.Proof511Cover
public import CFSG.CGT.Foote82.T66.Proof511PSL43
public import CFSG.CGT.Foote82.T66.Proof511SylSpor
public import CFSG.CGT.Foote82.T66.Proof511SylJ3
public import CFSG.CGT.Foote82.T66.Proof511SylMcL
public import CFSG.Milestones.CL_LIT_GH74_sectional_two_rank_four
public import CFSG.CGT.Foote82.T66.Proof511SylLie

public section

namespace CFSG.CGT.Foote82.Proof511

open Subgroup CFSG.Open CFSG.Quasithin.G11

section GH74

theorem gh74ModelsForm
    : CFSG.GH74.ModelsFormStatement := fun G _ _ _ hnonab hrank hsect =>
  CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models G hnonab hrank hsect

end GH74

section Cover

theorem psp43Cover_holds : PSp43Cover := fun _ _ _ hq hZ hS => center_eq_bot_of_psp43 hq hZ hS

end Cover

section CaseIIa

theorem caseIILemma511a_holds
    : CaseIILemma511a := by
  intro V _ _ _ X J L z c hJX hJn hJi hCJ hJq hZ hzX hz hL ⟨e⟩ _ _ hcL hc3 hdim hsyl
  obtain ⟨hAs, hAn⟩ := alt_simple_nonab (k := 6) (Or.inl rfl)
  have hLs : IsSimpleGroup ↥L := e.isSimpleGroup
  have hLn : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hAn
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul, h]))⟩
  haveI : Finite (GLV V) :=
    Finite.of_injective (fun f : GLV V => (f : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)
  have h : Hyp X J L z := ⟨hJX, hJn, hJi, hCJ, hJq, hZ, hzX, hz, hL, hLs, hLn⟩
  rcases reduce_a gh74ModelsForm CFSG.SeitzReduction.gls3OddLieAutComponentsInput
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
      (fun _ _ _ hY P => sqOne_card_M22 hY P) (fun _ _ _ hY P => sqOne_card_M23 hY P)
      (fun _ _ _ hY P => sqOne_card_J2 hY P) (fun _ _ _ hY P => sqOne_card_J3 hY P)
      (fun _ _ _ hY P => sqOne_card_McL hY P)
      (fun _ _ _ _ _ hp hp2 h8 hY P => sqOne_card_PSU4 hp hp2 h8 hY P) h (Or.inl ⟨e⟩) hsyl with
    h10 | h11 | hPSL
  · exact Or.inl h10
  · exact Or.inr h11
  · exfalso
    have hcJ : c ∈ J := h.le_J hcL
    refine not_psl43 hJq hZ hcJ hc3 ?_ hdim hPSL
    intro hcen
    have hcLc : (⟨c, hcL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hcen ⟨(g : GLV V), h.le_J g.2⟩)
      exact Subtype.ext this
    rw [center_eq_bot_of_simple hLn, Subgroup.mem_bot] at hcLc
    have hc1 : c = 1 := congrArg Subtype.val hcLc
    rw [hc1, orderOf_one] at hc3
    exact absurd hc3 (by norm_num)

end CaseIIa

section CaseIIb

theorem caseIILemma511b_holds
    : CaseIILemma511b := by
  intro V _ _ _ X J L z c hJX hJn hJi hCJ hJq hZ hzX hz hL ⟨e⟩ _ _ _ _ _ hsyl
  obtain ⟨hAs, hAn⟩ := alt_simple_nonab (k := 6) (Or.inl rfl)
  have hLs : IsSimpleGroup ↥L := e.isSimpleGroup
  have hLn : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hAn
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul, h]))⟩
  haveI : Finite (GLV V) :=
    Finite.of_injective (fun f : GLV V => (f : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)
  have h : Hyp X J L z := ⟨hJX, hJn, hJi, hCJ, hJq, hZ, hzX, hz, hL, hLs, hLn⟩
  rcases reduce_b gh74ModelsForm h (Or.inl ⟨e⟩) hsyl with h8 | h9 | hS
  · exact Or.inl h8
  · exact Or.inr (Or.inl h9)
  · refine Or.inr (Or.inr ?_)
    have hZ1 : center ↥J = ⊥ := center_eq_bot_of_psp43 hJq hZ hS
    have eJ : ↥J ≃* ↥J ⧸ center ↥J :=
      ((QuotientGroup.quotientMulEquivOfEq hZ1).trans QuotientGroup.quotientBot).symm
    rcases hS with ⟨-, hadm, K, iK, fK, hcard, ⟨eK⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact ⟨hadm, K, iK, fK, hcard, ⟨eJ.trans eK⟩⟩
    all_goals exact absurd h0 (by norm_num)

end CaseIIb

end CFSG.CGT.Foote82.Proof511
