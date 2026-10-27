module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma315
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherGoldschmidtFour

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

theorem goldschmidtEscape : GoldschmidtEscape := by
  intro G _ _ T V hT hVT hV hwc hnsc
  obtain ⟨P, hP⟩ := exists_sylow_eq_of_isSylowOf_top hT
  subst hP
  obtain ⟨U, hUV, h, h1, h2, h3⟩ :=
    GoldschmidtFour.goldschmidt_theorem_four_holds G P V hVT hV hwc hnsc
  exact ⟨U, hUV, h, h1, h2, h3⟩

end CFSG.ComponentClassification.Asc76X
