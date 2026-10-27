module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFrame
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropNine
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTenB
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropElevenB
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTwelveC
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinalB

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

theorem noSimpleCentralizerTwoANine_of_stepFinal
    (hfin : JankoStepFinal) :
    NoSimpleCentralizerTwoANine :=
  noSimpleCentralizerTwoANine_of_steps jankoFrameExists jankoStep7 jankoStep9 jankoStep10
    jankoStep11 jankoStep12 hfin

theorem noSimpleCentralizerTwoANine
    : NoSimpleCentralizerTwoANine :=
  noSimpleCentralizerTwoANine_of_stepFinal jankoStepFinal

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
