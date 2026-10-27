module

public import CFSG.LargeExtraspecial.S11MbSeven
public import CFSG.LargeExtraspecial.S11MaParity
public import CFSG.LargeExtraspecial.S11Nine

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4

universe u_G

variable {G : Type u_G} [Group G] [Finite G]

theorem timmesfeld11_8M2 (S : Setting G) : Timmesfeld11_8M2 S := by
  intro hCE g t τ u hy K hn
  by_cases h7 : 7 ≤ S.width
  · exact K.not_two_of_seven_le hy hCE h7
  · exact K.finrank_ne_two_of_even_width hy ⟨3, by omega⟩

end CFSG.LargeExtraspecial.S11
