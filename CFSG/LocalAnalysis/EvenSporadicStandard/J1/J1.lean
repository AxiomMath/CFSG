module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.CaseII
public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.FromJ1
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.J1
public import CFSG.Milestones.CL_LIT_Walter_abelian_Sylow_two_simple

public section

namespace CFSG.EvenSporadicStandard.J1Std

open Subgroup CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G]

theorem walterAbelian_of_milestone
    : WalterAbelian :=
  fun G _ _ _ hnonab P hP => CFSG.Milestones.cl_lit_walter_abelian_sylow_two_simple G hnonab P hP

theorem j1_not_standard
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L) :
    ¬ IsSporadic L .J1 := by
  intro hL
  have hI := hypothesisOne_quotient_of_isSporadic_J1 hL HypOne.J1.hypothesisOne_native
  obtain ⟨H, -⟩ := Setting.exists_of_stdHyp h hL hI
  exact false_of_step walterAbelian_of_milestone H
    (ascentStep_of_caseTwoImpossible (caseTwoImpossible H))

end CFSG.EvenSporadicStandard.J1Std
