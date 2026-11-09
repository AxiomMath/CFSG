module

public import CFSG.CGT.T75JM.N0ModelInputs
public import CFSG.CGT.T75JM.PData

public section

namespace CFSG.CGT.T75JM

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

@[expose] def tabEq (w w' : List (Fin 6 × Bool)) : Bool := n0Tab w == n0Tab w'

@[expose] def allVV (f : V3 → V3 → Bool) : Bool := decide (∀ c d : V3, f c d = true)

theorem allVV_spec {f : V3 → V3 → Bool} (h : allVV f = true) : ∀ c d, f c d = true := by
  unfold allVV at h
  exact of_decide_eq_true h

theorem allVV_intro {f : V3 → V3 → Bool} (h : ∀ c d, f c d = true) : allVV f = true := by
  unfold allVV
  exact decide_eq_true h

@[expose] def allVVInj (f : V3 → V3 → Bool) : Bool :=
  decide (∀ c d : V3, f c d = true → c = d)

theorem allVVInj_spec {f : V3 → V3 → Bool} (h : allVVInj f = true) :
    ∀ c d, f c d = true → c = d := by
  unfold allVVInj at h
  exact of_decide_eq_true h

theorem allVVInj_intro {f : V3 → V3 → Bool} (h : ∀ c d, f c d = true → c = d) :
    allVVInj f = true := by
  unfold allVVInj
  exact decide_eq_true h

@[expose] def allVBoth (f g : V3 → Bool) : Bool := decide (∀ c : V3, f c = true ∧ g c = true)

theorem allVBoth_spec {f g : V3 → Bool} (h : allVBoth f g = true) :
    ∀ c, f c = true ∧ g c = true := by
  unfold allVBoth at h
  exact of_decide_eq_true h

theorem allVBoth_intro {f g : V3 → Bool} (h : ∀ c, f c = true ∧ g c = true) :
    allVBoth f g = true := by
  unfold allVBoth
  exact decide_eq_true h

@[expose] def eMulCheck : Bool :=
  allVV fun c d => tabEq (vExp (eW c) ++ vExp (eW d)) (vExp (eW (c + d)))

@[expose] def eInjCheck : Bool :=
  allVVInj fun c d => tabEq (vExp (eW c)) (vExp (eW d))

@[expose] def eTorsCheck : Bool :=
  tabEq (vExp (eW (Pi.single 0 1))) [(2, true), (3, true), (4, true)] &&
    decide ((Pi.single 0 1 : V3) ≠ 0)

@[expose] def actVCheck : Bool :=
  allVBoth (fun c => tabEq (vGen 0 ++ vExp (eW c) ++ invWord (vGen 0)) (vExp (eW (glAct mV1 c))))
    fun c => tabEq (vGen 1 ++ vExp (eW c) ++ invWord (vGen 1)) (vExp (eW (glAct mV2 c)))

@[expose] def actGCheck : Bool :=
  allVBoth (fun c => tabEq (dExp (dW c)) (vExp (eW c)))
    fun c => tabEq (thExp (dW c)) (vExp (eW (glAct mG c)))

@[expose] def thetaCheck : Bool :=
  tabEq (dExp uW) (vExp wA) && tabEq (thExp uW) (vExp wB)

@[expose] def d8Check : Bool :=
  tabEq (vExp (sV ++ sV)) [] && tabEq (vExp (rV ++ rV ++ rV ++ rV)) [] &&
    tabEq (vExp (sV ++ rV ++ sV ++ rV)) [] &&
    decide (∀ c : V3,
      tabEq (vExp sV ++ vExp (eW c) ++ invWord (vExp sV)) (vExp (eW (glAct mS c))) = true ∧
      tabEq (vExp rV ++ vExp (eW c) ++ invWord (vExp rV)) (vExp (eW (glAct mR c))) = true)

end CFSG.CGT.T75JM
