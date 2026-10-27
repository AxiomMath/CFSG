module

public import CFSG.LargeExtraspecial.AS35YUMod
public import CFSG.LargeExtraspecial.AS35YUSp
public import CFSG.LargeExtraspecial.AS35YTMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions

namespace S14

section Certified

theorem asc512FixOddStmt : Asc512FixOddStmt := by
  intro G _ _ S hS hst hnd m hfam hdim r hrW hrU hr hR
  have hr0 : r ≠ 0 := fun h => by
    rw [h, QuadraticMap.map_zero] at hr
    exact zero_ne_one hr
  rcases hfam with ⟨rfl, hL⟩ | ⟨hm, hL⟩ | ⟨rfl, hL⟩
  · exact Setting.false_of_odd_psl4_YU hS hst hnd hL hdim hrW hrU hr0
  · exact Setting.false_of_odd_psp_YU hS hst hnd hm hL hdim hrW hrU hr hR
  · exact Setting.false_of_odd_pomega4_YU hS hst hnd hL hdim

theorem asc512FixFreeStmt_proof :
    Asc512FixFreeStmt :=
  asc512FixFreeStmt_of_odd asc512FixOddStmt

end Certified

end S14

end CFSG.LargeExtraspecial
