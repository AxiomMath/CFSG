module

public import CFSG.ClassicalInvolution.SubnormalClosure.Reduction
public import CFSG.ClassicalInvolution.Reduction
import CFSG.Adapters.GeneralizedFitting
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open

theorem genFittingFStar_normal (G : Type*) [Group G] : (genFittingFStar G).Normal :=
  CFSG.ComponentClassification.GeneralizedFitting.normal G

theorem partOne_of_aschbacherCIT (h : AschbacherCIT) : PartOne := by
  intro G _ _ _ hFnonab z hz J hzJ hJ _ _ hw _
  have : (genFittingFStar G).Normal := genFittingFStar_normal G
  have hFc : IsComponentOf (genFittingFStar G) ⊤ :=
    isComponentOf_top_of_normal_simple _ hFnonab
  have hC : Subgroup.centralizer (genFittingFStar G : Set G) = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    have hxF : x ∈ genFittingFStar G := CFSG.Adapters.generalized_fitting_self_centralizing G hx
    have hcen : (⟨x, hxF⟩ : genFittingFStar G) ∈ Subgroup.center (genFittingFStar G) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx g.1 g.2)
    rw [CFSG.ComponentClassification.Helpers.center_eq_bot _ hFnonab, Subgroup.mem_bot] at hcen
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hcen)
  have hO : classicalInvolutionOddCore G = ⊥ := by
    have : Group.IsSolvable (classicalInvolutionOddCore G) :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ (CFSG.ComponentClassification.OddCore.odd_card G)
    have hsub : IsSubnormal (classicalInvolutionOddCore G) ⊤ :=
      isSubnormal_of_normal_subgroupOf le_top inferInstance
    have hcomm := CFSG.ComponentClassification.LocalComponents.commutes_with_solvable_subnormal
      (genFittingFStar G) (classicalInvolutionOddCore G) hFc hsub
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer, hC] at hcomm
    exact le_bot_iff.mp hcomm
  exact oddLieType_or_isSporadic_of_aschbacherCIT h (genFittingFStar G) hFnonab hC hO hz hzJ hJ hw

end CFSG.ClassicalInvolution
