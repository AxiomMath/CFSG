module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8TenTwelveAux.Ten
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8TenTwelveAux.Twelve
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerBase
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false


theorem innerPlaneBalanceAt_E8_ten : InnerPlaneBalanceAt .E8 10 := by
  intro q hv p hp hp7 _ _ he
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  rw [← hK] at he
  exact InnerPlaneBalance.of_mulEquiv e (innerPlaneBalance_adjointE8_ten K hp hp7 he)

theorem innerPlaneBalanceAt_E8_twelve : InnerPlaneBalanceAt .E8 12 := by
  intro q hv p hp hp7 _ _ he
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  rw [← hK] at he
  exact InnerPlaneBalance.of_mulEquiv e (innerPlaneBalance_adjointE8_twelve K hp hp7 he)

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
