module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XFinal
public import CFSG.LocalAnalysis.ComponentClassification.Asc75Theorem3
public import CFSG.LocalAnalysis.ComponentClassification.Asc76L26Lemma26
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Lemma22PartFour
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.Asc76

theorem goldschmidtTheoremA : GoldschmidtTheoremA :=
  CFSG.Milestones.cl_lit_goldschmidt_strongly_closed_abelian

theorem lemma22Four : Lemma22Four :=
  fun _ _ _ _ _ _ _ hK hJ hKJ hfac hT hT1 hR hTR _ hmJ hTJ =>
    Lemma22.commutator_le_or_isElemAbelian AschbacherTheorem3.theorem_3_holds hK hJ hKJ hfac hT
      hT1 hR hTR hmJ hTJ

theorem asc76Theorem1_of_lemma28 (h28 : Asc76Lemma28) : Asc76Theorem1 :=
  asc76Theorem1_of lemma22Four L26.asc76Lemma26 h28 goldschmidtTheoremA

theorem asc76Theorem4_of_lemma28 (h28 : Asc76Lemma28) : Asc76Theorem4 :=
  asc76Theorem4_of lemma22Four L26.asc76Lemma26 h28 goldschmidtTheoremA

end CFSG.ComponentClassification.Asc76X
