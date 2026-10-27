module

public import CFSG.CGT.T75M23.P7Data

public section

namespace CFSG.CGT.T75M23

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.CGT.T75JM (V3 glAct)

@[expose] def tabEq7 (w w' : Word6) : Bool := n7Tab w == n7Tab w'

@[expose] def allV3V3 (f : V3 → V3 → Bool) : Bool := decide (∀ c d : V3, f c d = true)

@[expose] def allFin2V3 (f g : Fin 2 → V3 → Bool) : Bool :=
  decide (∀ (k : Fin 2) (c : V3), f k c = true ∧ g k c = true)

@[expose] def eMulCheck7 : Bool :=
  allV3V3 fun c d => tabEq7 (vExp7 (eW7 c) ++ vExp7 (eW7 d)) (vExp7 (eW7 (c + d)))

@[expose] def eInjCheck7 : Bool :=
  decide (∀ c d : V3, tabEq7 (vExp7 (eW7 c)) (vExp7 (eW7 d)) = true → c = d)

@[expose] def eTorsCheck7 : Bool :=
  tabEq7 (vExp7 (eW7 (Pi.single 2 1))) [(2, true), (5, true)] &&
    decide ((Pi.single 2 1 : V3) ≠ 0)

@[expose] def actVCheck7 : Bool :=
  decide (∀ c : V3,
    tabEq7 (vGen7 0 ++ vExp7 (eW7 c) ++ invWord7 (vGen7 0)) (vExp7 (eW7 (glAct mV17 c))) = true ∧
    tabEq7 (vGen7 1 ++ vExp7 (eW7 c) ++ invWord7 (vGen7 1)) (vExp7 (eW7 (glAct mV27 c))) = true)

@[expose] def actGCheck7 : Bool :=
  allFin2V3 (fun _ c => tabEq7 (dExp7 (dW7 c)) (vExp7 (eW7 c)))
    fun k c => tabEq7 (thExp7 k (dW7 c)) (vExp7 (eW7 (glAct mG7 c)))

@[expose] def thetaCheck7 : Bool :=
  tabEq7 (dExp7 uW7) (vExp7 wA7) && tabEq7 (thExp7 0 uW7) (vExp7 wB7)

@[expose] def d0Check7 : Bool := tabEq7 (d0W7 1) (vExp7 wD07)

@[expose] def d8Check7 : Bool :=
  tabEq7 (vExp7 (sV7 ++ sV7)) [] && tabEq7 (vExp7 (rV7 ++ rV7 ++ rV7 ++ rV7)) [] &&
    tabEq7 (vExp7 (sV7 ++ rV7 ++ sV7 ++ rV7)) [] &&
    decide (∀ c : V3,
      tabEq7 (vExp7 sV7 ++ vExp7 (eW7 c) ++ invWord7 (vExp7 sV7)) (vExp7 (eW7 (glAct mS7 c))) =
          true ∧
      tabEq7 (vExp7 rV7 ++ vExp7 (eW7 c) ++ invWord7 (vExp7 rV7)) (vExp7 (eW7 (glAct mR7 c))) =
          true)

end CFSG.CGT.T75M23
