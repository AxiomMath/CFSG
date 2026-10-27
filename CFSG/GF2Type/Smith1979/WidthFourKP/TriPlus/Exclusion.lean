module

public import CFSG.GF2Type.Smith1979.WidthFourKP.TriPlus.Build
public import CFSG.GF2Type.Smith1979.WidthFourKP.TriConf.LocalIndex

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

theorem widthFourOmegaTrialityFalse
    : WidthFourOmegaTrialityFalse := by
  intro G _ _ _ _ _ _ S hw hno hirr g H C t ht ht1 hVQ hΩ h4 hplus hiso hT
  obtain ⟨k, M1, T, hM⟩ := TriPlus.exists_triLocal hw hno hirr H C ht ht1 hVQ hΩ h4 hplus hiso hT
  exact TriConf.false_of_triLocal_of_plusTypeAt hw hno hirr H C ht ht1 hVQ hΩ h4 T hplus hM

end CFSG.GF2Type.Smith1979

end
