module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L2b
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsAutL2Rank

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

theorem cfL2Rank : GSThmB.CFL2Rank := by
  intro Y _ _ p f hp hp2 hf hY E hE
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hY
  rw [← Subgroup.card_map_of_injective (f := (autEquiv e).toMonoidHom) (autEquiv e).injective]
  exact pGammaL2_card_le_eight_of_sq (isOddPrimePower_of hp hp2 hf hF) _
    (sq_eq_one_map_autEquiv e E hE)

end CFSG.ComponentClassification.AutL2Facts
