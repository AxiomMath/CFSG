module

public import CFSG.LocalAnalysis.ComponentClassification.QuaternionComponentWired17
public import CFSG.ClassicalInvolution.Q3.TA3LiftQ8b
public import CFSG.ClassicalInvolution.Q3.TA3SmallLeavesTwin
public import CFSG.ClassicalInvolution.Q3.TA3FrameSplit

public section

namespace CFSG.ComponentClassification.QuaternionComponent

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.MilestoneAssembly

set_option linter.unusedSectionVars false

structure WiredInputs₁₈ : Prop where
  gh74 : GH74SectionalModels
  f1 : Q3.TightF1S fun m => Q3.CIT3Below m ∧ Q3.TightBelow m
  twistAllTwin : ∀ n, Q3.TightTwistAllTwin n
  largeLiftS : ∀ n, Q3.TightLargeLiftS n
  centTwin : ∀ n, Q3.TightCentTwinLift n
  twin2M12 : Q3.TA3.Twin2M12Leaf
  twin2Sz8 : Q3.TA3.Twin2Sz8Leaf
  twin2An : Q3.TA3.Twin2AnLeaf
  frameSmall : Q3.TA3.ResidualCFrameSmall
  frameLarge : Q3.TA3.ResidualCFrameLarge

section Wired


theorem WiredInputs₁₈.toWired₁₇
    (h : WiredInputs₁₈) : WiredInputs₁₇ where
  gh74 := h.gh74
  tightLift := fun hGH => Q3.TA3.tightHasMember3LargeBelowQ8_of_leaves₂ h.f1 h.twistAllTwin
    (Q3.TA3.tightSmallBase_of_twin hGH h.twin2M12 h.twin2Sz8 h.twin2An) h.largeLiftS h.centTwin
  frame := Q3.TA3.residualCFrame_of_ranges h.frameSmall h.frameLarge

theorem milestone_of_wired₁₈
    (h : WiredInputs₁₈)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hJ : Assembly.IsComponentOf J (Subgroup.centralizer ({z} : Set G)))
    (hzJ : z ∈ J) (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    Assembly.ComponentType.OddLieType G ∨ Nonempty (G ≃* Assembly.ComponentType.M11) :=
  milestone_of_wired₁₇ h.toWired₁₇ G hnonab z hz J hJ hzJ S hS

end Wired

end CFSG.ComponentClassification.QuaternionComponent
