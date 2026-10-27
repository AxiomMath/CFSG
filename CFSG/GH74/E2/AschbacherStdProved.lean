module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundationFinal
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL33
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoM11

public section

namespace CFSG.GH74.E2

theorem aschbacherStandardL33_proved :
    AschbacherStandardL33 :=
  ComponentClassification.RankTwoL33.aschbacherStandardL33_of
    ComponentClassification.RankTwoFoundation.lemma33Three

theorem aschbacherStandardM11_proved :
    AschbacherStandardM11 :=
  ComponentClassification.RankTwoM11.aschbacherStandardM11_of
    ComponentClassification.RankTwoFoundation.lemma32
    ComponentClassification.RankTwoFoundation.lemma33Three

end CFSG.GH74.E2
