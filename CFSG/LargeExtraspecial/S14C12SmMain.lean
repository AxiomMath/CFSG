module

public import CFSG.LargeExtraspecial.S14C12THyp
public import CFSG.LargeExtraspecial.S14C12SmGraph
public import CFSG.LargeExtraspecial.S14C12SmHolt

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open CFSG.Timmesfeld.Connectivity CFSG.RankThree.PartTwo.Sec21

theorem smithU62ThreeFourInput_of (hAS : AschbacherSmithWideInput)
    (hDW : DW.DW37Statement) (hHolt : HoltUniqueFixedPointSimple) (hLoc : SmithU62LocalInput)
    (hPath : SmithU62PathInput) : SmithU62ThreeFourInput := by
  intro G _ _ _ S hw hU
  obtain ⟨d, e, hd, he, h4⟩ := SmithQ.exists_isConj_orderOf_mul_eq_four hAS hDW S hw hU
  refine ⟨fun a b ha hb => ?_, ⟨d, e, hd, he, h4⟩⟩
  have hra := SmithHolt.reach_conjugatesOf hHolt S hw hU hd he h4 ha
  have hrb := SmithHolt.reach_conjugatesOf hHolt S hw hU hd he h4 hb
  obtain ⟨v, hv, hav, hvb⟩ :=
    SmithGraph.exists_common_of_reach (hPath G S hw hU) ha (reach_trans (reach_symm hra) hrb)
  exact SmithGraph.threeFour_of_common S (SmithGraph.local_of_input hLoc S hw hU) ha hb hv hav hvb

end CFSG.LargeExtraspecial.S14
