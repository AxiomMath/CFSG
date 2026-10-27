module

public import CFSG.LargeExtraspecial.DWCaseIIBNoSp
public import CFSG.LargeExtraspecial.DWW4.ReducibleWidthFour

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

theorem dw41WidthFourStatement_holds : DW41WidthFourStatement := by
  intro G _ _ _ S A _ hA hM hw hQonly hconj hSp
  obtain ⟨g, hgA, hgz⟩ := hconj
  exact MaxEA.false_of_spConfig hA hM hQonly (by omega) hgA hgz hSp

theorem dw37WidthFourStatement_holds :
    DW37WidthFourStatement :=
  dw37WidthFourStatement_of_dw41' dw41WidthFourStatement_holds

end CFSG.LargeExtraspecial.DW
