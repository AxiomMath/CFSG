module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Red
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Bar
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Final

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem input11_3_of_tables (T : Tables112) (TL : TableL2) : Input11_3 :=
  input11_3_of_I112 (i112_of_red (i112Red_of_tables T TL))

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
