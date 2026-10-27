module

public import CFSG.GF2Type.Smith1979.WidthFourKP.Swap.Input
public import CFSG.GF2Type.Smith1979.WidthFourKP.Swap.Contra
public import CFSG.GF2Type.Smith1979.WidthFourKP.Swap.Model
public import CFSG.LargeExtraspecial.S4CEMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

open CFSG.LargeExtraspecial

theorem widthFourSwapFalse_of_centralExtInput (hCE : S4.CentralExtInput.{0}) :
    WidthFourSwapFalse := by
  rintro G _ _ _ - hchar - S hw hno - g H C ⟨D⟩
  obtain ⟨x, K, Y, T⟩ := W4Swap.exists_thompsonInput W4Swap.hermStabFacts hCE hw hno H C D
  exact W4Swap.false_of_thompsonInput hchar H C hw T

theorem widthFourSwapFalse :
    WidthFourSwapFalse :=
  widthFourSwapFalse_of_centralExtInput S4.centralExtInput

end CFSG.GF2Type.Smith1979
