module

public import CFSG.ClassicalInvolution.Asc77.AscT7QMain
public import CFSG.ClassicalInvolution.Asc77.AscT7F2Main
public import CFSG.ClassicalInvolution.Asc77.AscT7G2Fus

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

namespace T7Q

variable {p f : ℕ} [Fact p.Prime]


theorem c25_20_inv_of_11_16 (h11 : C25_11 p f) (h16 : C25_16 p f) : C25_20_inv p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp h4 t' _ _ _ _ _
  exfalso
  exact hyp.std.1.cex (Or.inr (twoSubgroupsFourGenerated_of_index_four hyp h11 h16 h4))

theorem c25_20_fus_of_11_16 (h11 : C25_11 p f) (h16 : C25_16 p f) : C25_20_fus p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp h4 t' _ _ _ _ _ s _ _ _ _ _
  exfalso
  exact hyp.std.1.cex (Or.inr (twoSubgroupsFourGenerated_of_index_four hyp h11 h16 h4))

theorem c25_20_of_11_16 (h11 : C25_11 p f) (h16 : C25_16 p f) : C25_20 p f :=
  T7G2.c25_20_of_ex h11 h16 (c25_20_ex_of_11_16 h11 h16)

theorem c25_E4_of_11_16 (h11 : C25_11 p f) (h16 : C25_16 p f) : C25_E4 p f :=
  c25_E4_of_idx (c25_17_idx_of_11_16 p f h11 h16) (c25_20_of_11_16 h11 h16)

end T7Q

end CFSG.ClassicalInvolution.Asc77
