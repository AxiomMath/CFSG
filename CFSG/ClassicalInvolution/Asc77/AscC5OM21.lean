module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM10
public import CFSG.ClassicalInvolution.Asc77.AscC5OM20

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O

open CFSG.ClassicalInvolution.Generic

variable {p f : ℕ} [Fact p.Prime]


theorem om5ExcClass_proved : Om5ExcClass p f := by
  intro Y _ _ Φ A A' z' a₀ b₀ hD β₁ β₂ hβ₁2 hβ₂2 hfix₁ hfix₂ hbig₁ hbig₂
  obtain ⟨fr⟩ := M.exists_frame hD
  have h5 := M.five_le_card_gf hD.five
  exact fr.excClass hD.odd (M.two_ne_zero_gf f hD.odd) (by omega) (odd_card_gf hD.odd hD.five)
    β₁ β₂ hβ₁2 hβ₂2 hfix₁ hfix₂ hbig₁ hbig₂

variable (p f) in
theorem modelFacts_proved : ModelFacts p f where
  invFixFour := om5InvFixFour_proved
  innerOfTwin := om5InnerOfTwin_proved
  twinOfInner := om5TwinOfInner_proved
  interchange := om5Interchange_proved
  zSwap := om5ZSwap_proved
  uSwapNotZ := om5USwapNotZ_proved
  excClass := om5ExcClass_proved
  centerless := om5Centerless_proved
  sl2PerfectAut := sl2PerfectAut_proved

end CFSG.ClassicalInvolution.Asc77.C5O
