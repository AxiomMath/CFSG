module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Main
public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Dihedral
public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Unique

public section

namespace CFSG.ComponentClassification.Asc76.Sec5

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b

theorem asc76Theorem2_of (h22 : Asc76Lemma22) (h75 : Asc75Theorem4) (h4' : Asc76Theorem4)
    (h3L : Asc76Theorem3Large) (h3F : Asc76Theorem3Four) : Asc76Theorem2 := by
  have hU : UniqueOfInverts := by
    intro G _ _ R C C' hR hCR hCn hC hinv hE hsq hcyc hC'R e
    exact eq_of_mulEquiv_of_inverts hR hCR hCn hC hinv hE hsq hcyc hC'R e
  have hD : DihedralConclusion := by
    intro G _ _ A hO hA g hg R hR hRd hm
    exact dihedral_conclusion h3L h3F hO hA hg hR hRd hm
  exact asc76Theorem2_of_aux h22 h75 h4' hU hD

end CFSG.ComponentClassification.Asc76.Sec5
