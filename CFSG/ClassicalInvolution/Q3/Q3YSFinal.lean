module

public import CFSG.ClassicalInvolution.Q3.Q3YSMain
public import CFSG.ClassicalInvolution.Q3.Q3YSModelSplit
public import CFSG.ClassicalInvolution.Q3.Q3YSModelExc
public import CFSG.ClassicalInvolution.Q3.Q3YSModelSU
public import CFSG.ClassicalInvolution.Q3.Q3YSModelMinus
public import CFSG.ClassicalInvolution.Q3.Q3YSModelSp4

public section

namespace CFSG.ClassicalInvolution.Q3.Q3YS

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank


theorem modelFourGroup3On_exceptional : ModelFourGroup3On fun t =>
    t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 ∨ t = .trialityD4 := by
  intro t n ht hfund hadm hne heven
  rcases ht with h | h | h | h | h | h | h
  · exact modelFourGroup3On_centerless t n (Or.inl h) hfund hadm hne heven
  · exact modelFourGroup3On_centerless t n (Or.inr (Or.inl h)) hfund hadm hne heven
  · exact modelFourGroup3On_split t n (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      hfund hadm hne heven
  · exact modelFourGroup3On_split t n (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
      hfund hadm hne heven
  · exact modelFourGroup3On_centerless t n (Or.inr (Or.inr (Or.inl h))) hfund hadm hne heven
  · exact modelFourGroup3On_centerless t n (Or.inr (Or.inr (Or.inr (Or.inr h)))) hfund hadm hne
      heven
  · exact modelFourGroup3On_centerless t n (Or.inr (Or.inr (Or.inr (Or.inl h)))) hfund hadm hne
      heven

theorem modelFourGroup3On_of_minus (hMinus : ModelFourGroup3On fun t => t = .POmegaMinus) :
    ModelFourGroup3On fun _ => True :=
  modelFourGroup3On_of_tags
    (modelFourGroup3On_split.mono fun _ ht => Or.inl ht)
    modelFourGroup3On_psu
    (modelFourGroup3On_split.mono fun _ ht => Or.inr (Or.inl ht))
    (modelFourGroup3On_split.mono fun _ ht => Or.inr (Or.inr (Or.inl ht)))
    (modelFourGroup3On_split.mono fun _ ht => Or.inr (Or.inr (Or.inr (Or.inl ht))))
    hMinus
    modelFourGroup3On_exceptional

theorem modelFourGroup3On_all : ModelFourGroup3On fun _ => True :=
  modelFourGroup3On_of_minus modelFourGroup3On_minus

theorem typeC3Shape_of_odd3 (h3 : Q3W.OddThreeFreeInput) : Q3Z.TypeC3Shape :=
  typeC3Shape_of_inputs h3 modelFourGroup3On_all sp4KleinQuat3

end CFSG.ClassicalInvolution.Q3.Q3YS
