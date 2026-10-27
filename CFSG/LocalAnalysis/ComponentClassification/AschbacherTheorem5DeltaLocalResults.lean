module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalEight
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalTen
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SixLocalResults

public section

namespace CFSG.ComponentClassification.AschbacherTheorem5

theorem sectionSixLocalResults_of_inputs (h3 : AschbacherTheorem3.Theorem3Statement)
    (hin : SectionSixInputs) : SectionSixLocalResults where
  lemma_6_5_one := fun hC => lemma_6_5_one hC
  lemma_6_5_two := fun hC => lemma_6_5_two h3 hin hC
  lemma_6_6 := fun hC => lemma_6_6 h3 hin hC
  lemma_6_7 := fun hC => lemma_6_7 h3 hin hC
  lemma_6_8 := fun hC => lemma_6_8 h3 hin hC
  lemma_6_9 := fun hC => lemma_6_9 h3 hin hC
  lemma_6_10 := fun hC => lemma_6_10 h3 hin hC

end CFSG.ComponentClassification.AschbacherTheorem5
