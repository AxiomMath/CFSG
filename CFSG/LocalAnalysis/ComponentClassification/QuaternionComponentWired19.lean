module

public import CFSG.LocalAnalysis.ComponentClassification.QuaternionComponentWired18
public import CFSG.ClassicalInvolution.Q3.TL3F1Main
public import CFSG.ClassicalInvolution.Q3.TA3Twin3M12
public import CFSG.ClassicalInvolution.Q3.TA3Twin3Sz8
public import CFSG.ClassicalInvolution.Q3.TA3Twin3Alt
public import CFSG.ClassicalInvolution.Q3.TA3FrameFinal

public section

namespace CFSG.ComponentClassification.QuaternionComponent

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.MilestoneAssembly

set_option linter.unusedSectionVars false

structure WiredInputs₁₉ : Prop where
  gh74 : GH74SectionalModels
  twistAllTwin : ∀ n, Q3.TightTwistAllTwin n
  largeLiftS : ∀ n, Q3.TightLargeLiftS n
  centTwin : ∀ n, Q3.TightCentTwinLift n
  frameLarge : Q3.TA3.ResidualCFrameLarge

section Wired


theorem WiredInputs₁₉.toWired₁₈
    (h : WiredInputs₁₉) : WiredInputs₁₈ where
  gh74 := h.gh74
  f1 := Q3.tightF1S_holds
  twistAllTwin := h.twistAllTwin
  largeLiftS := h.largeLiftS
  centTwin := h.centTwin
  twin2M12 := Q3.TA3.twin2M12Leaf_holds
  twin2Sz8 := Q3.TA3.twin2Sz8Leaf_holds
  twin2An := Q3.TA3.twin2AnLeaf_holds
  frameSmall := Q3.TA3.Frame.residualCFrameSmall_of_gh74 h.gh74
  frameLarge := h.frameLarge

theorem milestone_of_wired₁₉
    (h : WiredInputs₁₉)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hJ : Assembly.IsComponentOf J (Subgroup.centralizer ({z} : Set G)))
    (hzJ : z ∈ J) (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    Assembly.ComponentType.OddLieType G ∨ Nonempty (G ≃* Assembly.ComponentType.M11) :=
  milestone_of_wired₁₈ h.toWired₁₈ G hnonab z hz J hJ hzJ S hS

end Wired

end CFSG.ComponentClassification.QuaternionComponent
