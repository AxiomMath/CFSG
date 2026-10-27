module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.SylowNormalizerControl

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G]

theorem card_subgroupOf_eq_inf (subgroup ambient : Subgroup G) :
    Nat.card (subgroup.subgroupOf ambient) = Nat.card ↥(subgroup ⊓ ambient) := by
  rw [← Subgroup.inf_subgroupOf_right]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv

theorem relIndex_mul_card_inf (subgroup ambient : Subgroup G) :
    subgroup.relIndex ambient * Nat.card ↥(subgroup ⊓ ambient) = Nat.card ambient := by
  rw [← card_subgroupOf_eq_inf]
  exact (subgroup.subgroupOf ambient).index_mul_card

variable {A : Type*} [Group A] [MulDistribMulAction A G]

end CFSG.DisconnectedInvolutionGraph.Helpers
