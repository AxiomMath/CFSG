module

public import CFSG.LargeExtraspecial.S12InspFamSmall

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.OrthogonalInvolutions

@[expose] def InspPSL4 : Prop := InspFor fun (X : Type) [Group X] (D : Set X) =>
  InspNondeg X D ∧ ∃ m, 4 ≤ m ∧ LieModel X .PSL m 2 1

theorem inspPSL_of (h4 : InspPSL4) : InspPSL := by
  intro G _ _ _ S g t haQ hne hn ht htA hS hred h
  obtain ⟨hND, m, hm, hL⟩ := h
  by_cases hm4 : 4 ≤ m
  · exact h4 G S g t haQ hne hn ht htA hS hred ⟨hND, m, hm4, hL⟩
  obtain rfl : m = 3 := by omega
  exact (Setting.false_of_lieModel_PSL32 haQ hne hn hS hL).elim

end CFSG.LargeExtraspecial
