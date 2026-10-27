module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearThreeTwo
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.DiagFamily

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem crossCharFamAt_A_regimeAThreeTwo : CrossCharFamAt .A regimeAThreeTwo :=
  crossCharFamAt_A_three_two

theorem crossCharFamCat_A_of_diagLinearBalance (hlin : DiagLinearBalance) :
    CrossCharFamCat .A :=
  crossCharFamCat_A_of_linear hlin crossCharFamAt_A_regimeAThreeTwo

theorem crossCharFamAt_not_regimeANondiag_iff :
    (CrossCharFamAt .A fun idx p => ¬ regimeANondiag idx p) ↔
      CrossCharFamAt .A regimeADiag := by
  constructor
  · intro h idx hk p hp hp2 hc hr
    exact h idx hk p hp hp2 hc ((not_regimeANondiag_iff hk).2 hr)
  · intro h idx hk p hp hp2 hc hr
    exact h idx hk p hp hp2 hc ((not_regimeANondiag_iff hk).1 hr)

end CFSG.HardMathSupport.Timmesfeld.CrossChar
