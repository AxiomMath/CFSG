module

public import CFSG.ClassicalInvolution.MilestoneAssemblyWired14
public import CFSG.ClassicalInvolution.Q3.Q3TMFSParts

public section

namespace CFSG.ClassicalInvolution.MilestoneAssembly.W15

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.Q3T.MFS
open CFSG.GH74.GLS.Balance CFSG.ClassicalInvolution.MilestoneAssembly.W14
open CFSG.Open (genFittingFStar IsSubnormal classicalInvolutionWitness
  classicalInvolutionTightlyEmbedded lieOrdersChar M11 classicalInvolutionM12)

structure WiredInputs₁₅ : Prop where
  gh74 : GH74SectionalModels
  tightLift : GH74SectionalModels → TightHasMember3LargeBelow
  smallOddLie : SmallOddLieTightMember
  frame : ResidualCFrame

set_option linter.unusedSectionVars false

theorem WiredInputs₁₅.toWired14 (hbal : SolvableL2PrimeBalance) (h : WiredInputs₁₅) :
    WiredInputs₁₄ where
  gh74 := h.gh74
  q3 := ⟨memberFreeSocleOuter3_of_gh74 hbal h.gh74 (h.tightLift h.gh74) h.smallOddLie h.frame⟩
  tightLift := fun hGH hI G _ _ _ hnab hlarge R S hS t ht hto hRC hRn h2 =>
    h.tightLift hGH (Nat.card G + 1) (fun Y _ _ _ Λ hΛ => hI Y Λ hΛ) G (Nat.lt_succ_self _) hnab
      hlarge R S hS t ht hto hRC hRn h2

theorem WiredInputs₁₅.models (hbal : SolvableL2PrimeBalance) (h : WiredInputs₁₅)
    (G : Type) [Group G] [Finite G]
    [IsSimpleGroup (genFittingFStar G)]
    (hFnonab : ∃ a b : genFittingFStar G, a * b ≠ b * a)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hzJ : z ∈ J) (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    (classicalInvolutionWitness J → CFSG.Blueprint.OddLieType (genFittingFStar G) ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11) ∧
    (classicalInvolutionTightlyEmbedded J → CFSG.Blueprint.OddLieType (genFittingFStar G) ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M12) :=
  (h.toWired14 hbal).models G hFnonab z hz J hzJ hJ S hS

end CFSG.ClassicalInvolution.MilestoneAssembly.W15
