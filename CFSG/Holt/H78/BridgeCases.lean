module

import CFSG.Holt.General.Defs
public import CFSG.Holt.H78.SEModel

public section

namespace CFSG.Holt.H78

open MulAction Subgroup CFSG.Holt CFSG.Holt.General

section Basic

variable {G : Type*} [Group G]

theorem le_of_normal_of_centralizer_eq_bot {N B : Subgroup G} [N.Normal] [B.Normal]
    [IsSimpleGroup B] (hC : centralizer (B : Set G) = ⊥) (hN : N ≠ ⊥) : B ≤ N := by
  have := (inferInstance : N.Normal).subgroupOf B
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf B) with h | h
  · refine absurd (le_bot_iff.mp ?_) hN
    rw [← hC, ← commutator_eq_bot_iff_le_centralizer]
    exact le_bot_iff.mp ((commutator_le_inf N B).trans (subgroupOf_eq_bot.mp h).le_bot)
  · exact subgroupOf_eq_top.mp h

end Basic

end CFSG.Holt.H78
