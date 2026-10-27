module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

theorem isSylowOf_inf_of_normal {H : Type} [Group H] [Finite H] {I D : Subgroup H} {p : ℕ}
    [Fact p.Prime] (hI : I.Normal) (hD : CFSG.ABGLocalTools.IsSylowOf p D ⊤) :
    CFSG.ABGLocalTools.IsSylowOf p (D ⊓ I) I :=
  hD.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top_iff.mpr hI).ge

end CFSG.LocalAnalysis.AGL81I.Section3
