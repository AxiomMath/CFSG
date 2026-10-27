module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitGH
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitInputs

public section

namespace CFSG.ComponentClassification.GHarris

theorem grsGorensteinHarrisInput_of_theoremA
    (hGH : HSFLit.GorensteinHarrisInput) : GrSLit.GorensteinHarrisInput := by
  intro G _ _ _ _ _ S T e
  exact HSFLit.gorensteinHarris_corollaryA hGH ⟨S, T, e⟩

end CFSG.ComponentClassification.GHarris
