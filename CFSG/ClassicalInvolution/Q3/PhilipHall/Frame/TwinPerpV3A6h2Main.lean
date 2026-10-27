module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6h2Glue

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6h2

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

variable {n : ℕ}

theorem v3AE6Glue_of (hI : V3AE6I n) (hR : AE6ModelAE8) (hT0 : AE6ModelEdgePairsMem)
    (hT : AE6ModelTri) : V3AE6Glue n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h H fr hx L₂ L₃ A₂ A₃ hD hS
  obtain ⟨-, A, hAspan, hAker, -⟩ := hI Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨B₂, hB₂span, hB₂ker, -⟩,
    ⟨B₃, hB₃span, hB₃ker, -⟩⟩ := hD
  refine ae6Glue_of_idents hS ?_ hR hT0 hT
  intro k
  fin_cases k
  · exact ⟨A, hAspan, hAker⟩
  · exact ⟨B₂, hB₂span, hB₂ker⟩
  · exact ⟨B₃, hB₃span, hB₃ker⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6h2
