module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L2b
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentral

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

theorem cfL2C : GSThmB.CFL2C := by
  intro Y _ _ p f hp hp2 hf hY T hT R hR hRT
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hY
  rw [← Subgroup.card_map_of_injective (f := (autEquiv e).toMonoidHom) (autEquiv e).injective]
  refine card_le_four_of_centralizes_sylow hp hp2 hf hF (sylowMap e T)
    (by rw [card_sylowMap]; exact hT) _ (hR.map _) ?_
  rw [coe_sylowMap]
  exact centralizes_map_autEquiv e T R hRT

end CFSG.ComponentClassification.AutL2Facts
