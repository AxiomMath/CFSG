module

public import CFSG.Goldschmidt.Final
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchur
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchurReeJ1
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightFinal
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixFinal

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

theorem theorem_3_holds : Theorem3Statement :=
  theorem_3_of_theorem_4_8
    (theorem_4_8_of_F2 CFSG.Goldschmidt.topStatement WalterSchur.walter_schur_two_part_holds
      (lemma_4_6 CFSG.Goldschmidt.topStatement WalterSchur.theorem3KnownGroupFacts_holds))

end CFSG.ComponentClassification.AschbacherTheorem3
