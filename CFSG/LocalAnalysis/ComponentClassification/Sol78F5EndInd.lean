module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78F514Basic

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.ComponentClassification.Foote5

variable {G : Type} [Group G] [Finite G]

namespace Hyp

variable {L₀ L Q S T : Subgroup G} {z t s : G} {𝕊 : Type} [Group 𝕊] [Finite 𝕊]
  {ε : L ⧸ pPrimeCore 2 L ≃* 𝕊} {Lin : Subgroup (MulAut 𝕊)} (H : Hyp L₀ L Q S T z t s ε Lin)
include H

theorem footeFamilyType_L : FooteFamilyType L := by
  obtain ⟨-, ⟨e⟩⟩ := H.sec5.memF
  rcases H.sec5.sec4.footeFamilyType with ⟨⟨e7⟩⟩ | ⟨p, f, hp, hp2, hf, h5, hL⟩
  · exact Or.inl ⟨e.trans e7⟩
  · exact Or.inr ⟨p, f, hp, hp2, hf, h5, LieType.CurtisTits.lieModel_of_mulEquiv e.symm hL⟩

end Hyp

end CFSG.ComponentClassification.Sol78.F514
