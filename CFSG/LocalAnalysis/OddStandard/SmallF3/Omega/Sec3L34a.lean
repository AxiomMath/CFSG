module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Inputs

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82Lemma34a_of_inputs (hT2 : Asc82Thm2Q) (hC1 : Asc82CommuteStep) :
    Asc82Lemma34a := by
  intro G _ _ t L hSet x X y K u I hD hu hmem hI hIF
  have hData : Sec3L34Data x X y K u I := ⟨hD, hu, hmem, hI, hIF⟩
  rcases hT2 G t L hSet x X y K u I hData with h | h
  · exact Or.inl (hC1 G t L hSet x X y K u I hData h)
  · exact Or.inr h

end CFSG.OddStandard.SmallF3.Omega
