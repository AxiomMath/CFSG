module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Thm3FourSmallA7
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Thm3FourOfSmall
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Thm3FourSmallU34

public section

namespace CFSG.ComponentClassification.Asc76X.Thm3Four

open CFSG.ComponentClassification.Asc76

theorem smallTightFour : SmallTightFour := by
  intro X _ _ hX K R S hK hKn hR hRe h4 hS hRS hwc
  rcases hX with he | he | he | he | he
  · obtain ⟨e⟩ := he
    exact local_of_psu3 e K R S hK hKn hR hRe h4 hS hRS hwc
  · exact local_of_small_psl2 (Or.inl he) K R S hK hKn hR hRe h4 hS hRS hwc
  · exact local_of_small_psl2 (Or.inr (Or.inl he)) K R S hK hKn hR hRe h4 hS hRS hwc
  · exact local_of_small_psl2 (Or.inr (Or.inr he)) K R S hK hKn hR hRe h4 hS hRS hwc
  · obtain ⟨e⟩ := he
    exact local_of_alt7 e K R hK hKn hR hRe h4

theorem asc76Theorem3Four :
    Asc76Theorem3Four :=
  asc76Theorem3Four_of_small smallTightFour

end CFSG.ComponentClassification.Asc76X.Thm3Four
