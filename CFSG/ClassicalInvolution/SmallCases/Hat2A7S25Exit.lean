module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Tight

public section

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution

@[expose] def A7ExitTF4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    3 ≤ twoRank G → TwoSubgroupsFourGenerated G →
      ∀ (K : Subgroup G) (z : G), Hat2A7.IsClassical2A7 ⊤ K z → False

end CFSG.ClassicalInvolution.Hat2A7S
