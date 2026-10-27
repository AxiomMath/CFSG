module

public import CFSG.ClassicalInvolution.Asc77.AscC22G12
public import CFSG.ClassicalInvolution.Asc77.AscC22G15
public import CFSG.ClassicalInvolution.Asc77.AscC22P18

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace C22G

set_option linter.unusedSectionVars false

section Final

variable {p f : ℕ} [Fact p.Prime]

theorem c22_layerNormAlpha_proved : C22_layerNormAlpha p f := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h
  have hp : p ≠ 2 := h.setting.stand.odd
  have hp2 : p % 2 = 1 := ((Fact.out : p.Prime).eq_two_or_odd).resolve_left hp
  have hodd : p ^ f % 2 = 1 := by rw [Nat.pow_mod, hp2]; simp
  have h4 : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by omega
  rcases h4 with h1 | h3
  · exact C22P.normY_of_hyp22 h1 h
  · exact normY_of_hyp22_psu h3 h

theorem c22_8Gen_proved : C22_8Gen p f := c22_8Gen_of_layerNormAlpha c22_layerNormAlpha_proved

end Final

end C22G

end CFSG.ClassicalInvolution.Asc77
