module

public import CFSG.Goldschmidt.Setup
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts

public section

open CFSG.Open
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

structure SectionSixGlobalInputs : Prop where
  theorem_3 : AschbacherTheorem3.Theorem3Statement
  lemma_4_6 : AschbacherTheorem3.Lemma46Statement
  theorem_4_8 : AschbacherTheorem3.Theorem48Statement
  goldschmidt : CFSG.Goldschmidt.TopStatement
  goldschmidt_type_automorphisms : AschbacherTheorem3.GoldschmidtTypeAutomorphisms

end CFSG.ComponentClassification.AschbacherTheorem5
