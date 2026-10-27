module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BabyCoverProved
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FixLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BabyP3Core

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp
  CFSG.Monster.B.TwoA.Amalgam CFSG.Open


theorem bFixesElem_of_oddMultTrivial (hmult : OddMultTrivial .B) : BFixesElem := by
  intro H _ _ L K u hcov hP
  have hL : IsSporadic L .B := hcov.isSporadic_of_mult hmult
  obtain ⟨Ψ, hΨ⟩ := babyCover_pairEquiv hL hP
  have hKC : K ≤ L ⊓ centralizer ({u} : Set H) := fun k hk =>
    ⟨hP.2.2.1 hk, mem_centralizer_singleton_iff.2 (hP.2.2.2.1 k hk)⟩
  let θ : ↥K ≃* ↥(commutator ↥Eam) :=
    (Subgroup.subgroupOfEquivOfLe hKC).symm.trans (subgroupEquivOfIff Ψ hΨ)
  exact fixes_of_mulEquiv θ bFix_commutator_Eam

end CFSG.EvenSporadicStandard.Induction
