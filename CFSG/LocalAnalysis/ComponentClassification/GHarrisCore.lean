module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisA4

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup HSFLit


theorem theoremACore_of (hC : GorensteinHaradaThmCInput)
    (hI48 : CFSG.Quasithin.HSType.StatementI48) : TheoremACore := by
  intro G _ _ hT hidx hOG
  obtain ⟨D₀⟩ := exists_ghSylow hT
  obtain ⟨D, -, hxa⟩ := D₀.exists_ghSylow_not_conj_x_a
  by_cases hB : D.caseB
  · exact D.conclusionA_B hC hidx hxa hB hOG
  · exact Or.inl (hI48 G (D.isTypeHS_A hC hidx hxa hB hOG))

theorem gorensteinHarrisInput_of (hC : GorensteinHaradaThmCInput)
    (hI48 : CFSG.Quasithin.HSType.StatementI48) : GorensteinHarrisInput :=
  gorensteinHarrisInput_of_core (theoremACore_of hC hI48)

end CFSG.ComponentClassification.GHarris
