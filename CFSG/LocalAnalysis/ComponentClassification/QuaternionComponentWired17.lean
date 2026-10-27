module

public import CFSG.LocalAnalysis.ComponentClassification.QuaternionComponentWired16
public import CFSG.ClassicalInvolution.Q3.TA3SOLFinal

public section

namespace CFSG.ComponentClassification.QuaternionComponent

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.MilestoneAssembly

set_option linter.unusedSectionVars false

structure WiredInputs₁₇ : Prop where
  gh74 : GH74SectionalModels
  tightLift : GH74SectionalModels → Q3.TA3.TightHasMember3LargeBelowQ8
  frame : Q3.Q3T.MFS.ResidualCFrame

section Wired

theorem WiredInputs₁₇.toWired₁₆ (h : WiredInputs₁₇) : WiredInputs₁₆ where
  gh74 := h.gh74
  tightLift := h.tightLift
  smallOddLie := Q3.TA3.smallOddLieTightMemberS_holds
  frame := h.frame

theorem milestone_of_wired₁₇ (h : WiredInputs₁₇)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hJ : Assembly.IsComponentOf J (Subgroup.centralizer ({z} : Set G)))
    (hzJ : z ∈ J) (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    Assembly.ComponentType.OddLieType G ∨ Nonempty (G ≃* Assembly.ComponentType.M11) :=
  milestone_of_wired₁₆ h.toWired₁₆ G hnonab z hz J hJ hzJ S hS

end Wired

end CFSG.ComponentClassification.QuaternionComponent
