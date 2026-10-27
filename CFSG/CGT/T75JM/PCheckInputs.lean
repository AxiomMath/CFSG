module

public import CFSG.CGT.T75JM.N0ModelInputs
public import CFSG.CGT.T75JM.PData

public section

namespace CFSG.CGT.T75JM

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

@[expose] def tabEq (w w' : List (Fin 6 × Bool)) : Bool := n0Tab w == n0Tab w'

@[expose] def eMulCheck : Bool :=
  decide (∀ c d : V3, tabEq (vExp (eW c) ++ vExp (eW d)) (vExp (eW (c + d))) = true)

@[expose] def eInjCheck : Bool :=
  decide (∀ c d : V3, tabEq (vExp (eW c)) (vExp (eW d)) = true → c = d)

@[expose] def eTorsCheck : Bool :=
  tabEq (vExp (eW (Pi.single 0 1))) [(2, true), (3, true), (4, true)] &&
    decide ((Pi.single 0 1 : V3) ≠ 0)

@[expose] def actVCheck : Bool :=
  decide (∀ c : V3,
    tabEq (vGen 0 ++ vExp (eW c) ++ invWord (vGen 0)) (vExp (eW (glAct mV1 c))) = true ∧
    tabEq (vGen 1 ++ vExp (eW c) ++ invWord (vGen 1)) (vExp (eW (glAct mV2 c))) = true)

@[expose] def actGCheck : Bool :=
  decide (∀ c : V3, tabEq (dExp (dW c)) (vExp (eW c)) = true ∧
    tabEq (thExp (dW c)) (vExp (eW (glAct mG c))) = true)

@[expose] def thetaCheck : Bool :=
  tabEq (dExp uW) (vExp wA) && tabEq (thExp uW) (vExp wB)

@[expose] def d8Check : Bool :=
  tabEq (vExp (sV ++ sV)) [] && tabEq (vExp (rV ++ rV ++ rV ++ rV)) [] &&
    tabEq (vExp (sV ++ rV ++ sV ++ rV)) [] &&
    decide (∀ c : V3,
      tabEq (vExp sV ++ vExp (eW c) ++ invWord (vExp sV)) (vExp (eW (glAct mS c))) = true ∧
      tabEq (vExp rV ++ vExp (eW c) ++ invWord (vExp rV)) (vExp (eW (glAct mR c))) = true)

end CFSG.CGT.T75JM
