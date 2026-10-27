module

public import CFSG.ClassicalInvolution.Q3.Q3PlanParams
public import CFSG.ClassicalInvolution.Q3.Q3PlanRankTwo

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

@[expose] def CITSectionalFour3 : Prop :=
  ∀ (F : Type) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
    ∀ (z : F) (K : Subgroup F), IsClassicalMember3 K z → 3 ≤ twoRank F →
      TwoSubgroupsFourGenerated F →
      Blueprint.OddLieType F ∨ Blueprint.NativeSporadic.IsSporadic F .M11

@[expose] def CoreStep3Large : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G →
      LieSystem3 G (Set.range fun g : G => conjSub g K)

theorem coreStep3_of_pieces (hup : SmallUpgrade3) (hs4 : CITSectionalFour3)
    (hlarge : CoreStep3Large) : CoreStep3 := by
  intro G _ _ _ hnab K z hK hBelow
  by_cases h2 : twoRank G ≤ 2
  · exact hup G hnab K z hK (citRankTwo3 G hnab z K hK h2)
  · by_cases h4 : TwoSubgroupsFourGenerated G
    · exact hup G hnab K z hK (hs4 G hnab z K hK (by omega) h4)
    · exact hlarge G hnab K z hK hBelow (by omega) h4

end CFSG.ClassicalInvolution.Q3
