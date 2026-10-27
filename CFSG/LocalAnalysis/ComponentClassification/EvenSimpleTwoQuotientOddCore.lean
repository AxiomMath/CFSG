module

public import CFSG.LocalAnalysis.ComponentClassification.TwoProductOddCore

public section

open CFSG.Open

namespace CFSG.ComponentClassification.EvenSimpleTwoQuotientOddCore

theorem trivial {G : Type*} [Group G] [Finite G]
    (normal : Subgroup G) [normal.Normal] [IsSimpleGroup normal]
    (heven : Even (Nat.card normal)) (hquotient : IsPGroup 2 (G ⧸ normal)) :
    componentClassificationOddCore G = ⊥ := by
  let core := componentClassificationOddCore G
  let : core.Characteristic := OddCore.characteristic G
  have hcontained : core ≤ normal := TwoProductOddCore.core_le_normal normal hquotient
  let intersection := core.subgroupOf normal
  have hnormal : intersection.Normal := inferInstance
  have hodd : Odd (Nat.card intersection) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcontained).toEquiv]
    exact OddCore.odd_card G
  have hintersectionBot : intersection = ⊥ := by
    rcases hnormal.eq_bot_or_eq_top with hbot | htop
    · exact hbot
    · rw [htop, Subgroup.card_top] at hodd
      exact ((Nat.not_even_iff_odd.mpr hodd) heven).elim
  have hmap := congrArg (Subgroup.map normal.subtype) hintersectionBot
  rw [Subgroup.map_subgroupOf_eq_of_le hcontained, Subgroup.map_bot] at hmap
  exact hmap

end CFSG.ComponentClassification.EvenSimpleTwoQuotientOddCore
