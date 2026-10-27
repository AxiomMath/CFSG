module

public import CFSG.ClassicalInvolution.Asc77.AscT7MQ
public import CFSG.ClassicalInvolution.Asc77.AscT7MZ

public section

namespace CFSG.ClassicalInvolution.Asc77

set_option linter.unusedSectionVars false

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic

variable (p : ℕ) [Fact p.Prime]


structure TwinSqOrth : Prop where
  plus : p ≠ 2 → ∀ e, 5 ≤ p ^ e → ∀ n, 4 ≤ n → StatedLieAdmissible .POmegaPlus n p e →
    (Even n ∨ p ^ e % 4 = 1) → TwinSqAlpha p e .POmegaPlus n
  minus : p ≠ 2 → ∀ e, 5 ≤ p ^ e → ∀ n, 4 ≤ n → StatedLieAdmissible .POmegaMinus n p e →
    Odd n → p ^ e % 4 = 3 → TwinSqAlpha p e .POmegaMinus n

theorem twinSqRest_of_orth (h : TwinSqOrth p) : TwinSqRest p where
  psu hp _ hq _ hadm := twinSqAlpha_psu4 hp hq hadm
  plus := h.plus
  minus := h.minus

theorem twinSqAlphaRows_of_orth (h : TwinSqOrth p) : TwinSqAlphaRows p :=
  twinSqAlphaRows_of_rest p (twinSqRest_of_orth p h)

end CFSG.ClassicalInvolution.Asc77
