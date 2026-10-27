module

public import CFSG.LargeExtraspecial.DWW4Rank
public import CFSG.LargeExtraspecial.S12ModDWMain
public import CFSG.LargeExtraspecial.A2ModMain
public import CFSG.Timmesfeld.ARSInputThm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW.W4Rank

theorem theoremAWidthFour_holds :
    TheoremAWidthFour := by
  intro G _ _ _ S hw hconj hred
  obtain ⟨g₀, hgQ, hg⟩ := hconj
  exact DW.exists_maxEA_of_isReducibleN CFSG.Timmesfeld.arsInput
    (DW.dw2OutInspectionInputN_of_cert DW.dw2FieldInput CFSG.LargeExtraspecial.s12ExcModuleInputN) (by omega) hgQ hg
    hred

end CFSG.LargeExtraspecial.DW.W4Rank
