module

public import CFSG.LocalAnalysis.ComponentClassification.Foote47NineMain
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFoote47GenA7
public import CFSG.LocalAnalysis.ComponentClassification.Foote47Inputs

public section

namespace CFSG.ComponentClassification.Foote47

theorem foote47FourgroupGeneration :
    Foote47FourgroupGeneration := by
  intro S _ _ hS T hT2 hF hnab
  rcases hS with he | ⟨p, f, hp, hp2, hf, -, hL⟩
  · obtain ⟨e⟩ := he
    exact AutL2Facts.foote47FourgroupGeneration_a7 e T hT2 hF hnab
  · by_cases h9 : p ^ f = 9
    · exact Nine.foote47FourgroupGeneration_nine h9 hL T hT2 hF hnab
    · exact AutL2Facts.foote47FourgroupGeneration_psl2 hp hp2 hf h9 hL T hF

end CFSG.ComponentClassification.Foote47
