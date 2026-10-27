module

public import CFSG.LocalAnalysis.ComponentClassification.QuaternionComponentWired14
public import CFSG.ClassicalInvolution.Q3.TA3MFSQ8
public import CFSG.GH74.GLS.Balance.Bender.Final

public section

namespace CFSG.ComponentClassification.QuaternionComponent

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.MilestoneAssembly

set_option linter.unusedSectionVars false

structure WiredInputs₁₆ : Prop where
  gh74 : GH74SectionalModels
  tightLift : GH74SectionalModels → Q3.TA3.TightHasMember3LargeBelowQ8
  smallOddLie : Q3.TA3.SmallOddLieTightMemberS
  frame : Q3.Q3T.MFS.ResidualCFrame

section Wired

theorem memberFreeSocle_of_wired₁₆ (h : WiredInputs₁₆) : Q3.Q3T.MemberFreeSocleOuter3 :=
  Q3.TA3.memberFreeSocleOuter3_of_gh74Q8 GH74.GLS.Balance.solvableL2PrimeBalance_proved h.gh74
    (h.tightLift h.gh74) h.smallOddLie h.frame

theorem milestone_of_wired₁₆ (h : WiredInputs₁₆)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hJ : Assembly.IsComponentOf J (Subgroup.centralizer ({z} : Set G)))
    (hzJ : z ∈ J) (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    Assembly.ComponentType.OddLieType G ∨ Nonempty (G ≃* Assembly.ComponentType.M11) :=
  milestone_of_gh74_memberFree h.gh74 (memberFreeSocle_of_wired₁₆ h) G hnonab z hz J hJ hzJ S hS

end Wired

end CFSG.ComponentClassification.QuaternionComponent
