module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Glue
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_NR
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Red
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_MinT
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_CaseJK
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_CaseJgt
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesB

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem input11_3_of_I112 (h112 : I112) : Input11_3 :=
  input11_3_of_kernel h112
    (kernel11_3a_of_core h112 (noL2RankBound_of_tables tables113)
      (noL2Reduced_of_cases tables113 minT113_proved (caseJK113_of_tables tables113) (caseJgt113_of_tables tables113)))

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
