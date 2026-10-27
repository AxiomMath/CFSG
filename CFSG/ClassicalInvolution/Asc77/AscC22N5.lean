module

public import CFSG.ClassicalInvolution.Asc77.AscC22N4
public import CFSG.ClassicalInvolution.Asc77.AscR31Phan

public section

namespace CFSG.ClassicalInvolution.Asc77

set_option linter.unusedSectionVars false

section Final

variable {p f : ℕ} [Fact p.Prime]


theorem R31.c22_phanChainNeg_proved : R31.C22_phanChainNeg p f := by
  intro hq3 G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ hs hW hLG
  exact C22N.chain_of_alpha_neg hq3 hs hW hLG.1 hLG.2
    (C22N.alpha_eq_bot_neg hq3 hs hW hLG.2)

end Final

end CFSG.ClassicalInvolution.Asc77
