module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerPSpU4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Row516NoPSp

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG Subgroup CFSG.ComponentClassification.GSThmB

theorem cfRow516InnerPSp : CFRow516InnerPSp := by
  intro H _ _ h hrow hin p f hp hp2 hf hJ ℓ hℓ2
  obtain ⟨hZ, p', f', hp', hp2', hf', hJ', hK⟩ := inner_structure h hrow hin
  obtain ⟨rfl, rfl⟩ := eq_of_lieModel_psl_two hp' hp2' hf' hp hp2 hJ' hJ
  rcases hK with ⟨hq, F, _, _, hF, ⟨e⟩⟩ | ⟨hq, K', _, hUF, ⟨e⟩⟩
  · exact innerPSp_L4 h hrow hin hp' hp2' hJ' hZ hq hF e ℓ hℓ2
  · exact innerPSp_U4 h hrow hin hp' hp2' hJ' hZ hq hUF e ℓ hℓ2

end CFSG.ComponentClassification.CatFactsL4U4
