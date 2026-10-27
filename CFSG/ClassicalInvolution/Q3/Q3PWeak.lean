module

public import CFSG.ClassicalInvolution.Q3.Q3EMain

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

@[expose] def CIT3LargeWeak : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G →
      Blueprint.OddLieType G ∨ Blueprint.NativeSporadic.IsSporadic G .M11

theorem coreStep3Large_of_weak (h : CIT3LargeWeak) : CoreStep3Large :=
  fun G _ _ _ hnab K z hK hBelow h3 h4 =>
    smallUpgrade3_proved G hnab K z hK (h G hnab K z hK hBelow h3 h4)

theorem coreStep3_of_pieces_weak (hs4 : CITSectionalFour3) (hlarge : CIT3LargeWeak) :
    CoreStep3 :=
  coreStep3_of_pieces smallUpgrade3_proved hs4 (coreStep3Large_of_weak hlarge)

theorem coreStep3_of_gh74_weak (hGH : GH74SectionalModels) (hNL : SectionalFourNonLie3)
    (hlarge : CIT3LargeWeak) : CoreStep3 :=
  coreStep3_of_gh74_proved hGH hNL (coreStep3Large_of_weak hlarge)

end CFSG.ClassicalInvolution.Q3

namespace CFSG.ClassicalInvolution.MilestoneAssembly

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3

theorem q3Inputs₅_of_residuals_weak (hGH : GH74SectionalModels) (hQ : QuasisimpleConnected3)
    (hNL : SectionalFourNonLie3) (hlarge : CIT3LargeWeak) : Q3Inputs₅ :=
  q3Inputs₅_of_residuals_proved hGH hQ hNL (coreStep3Large_of_weak hlarge)

end CFSG.ClassicalInvolution.MilestoneAssembly
