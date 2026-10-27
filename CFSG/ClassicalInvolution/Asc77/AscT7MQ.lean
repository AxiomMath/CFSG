module

public import CFSG.ClassicalInvolution.Asc77.AscT7MI
public import CFSG.ClassicalInvolution.Asc77.AscT7MP

public section

namespace CFSG.ClassicalInvolution.Asc77

set_option linter.unusedSectionVars false

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic

variable (p : ℕ) [Fact p.Prime]


structure TwinSqRest : Prop where
  psu : p ≠ 2 → ∀ e, 5 ≤ p ^ e → p ^ e % 4 = 3 → StatedLieAdmissible .PSU 4 p e →
    TwinSqAlpha p e .PSU 4
  plus : p ≠ 2 → ∀ e, 5 ≤ p ^ e → ∀ n, 4 ≤ n → StatedLieAdmissible .POmegaPlus n p e →
    (Even n ∨ p ^ e % 4 = 1) → TwinSqAlpha p e .POmegaPlus n
  minus : p ≠ 2 → ∀ e, 5 ≤ p ^ e → ∀ n, 4 ≤ n → StatedLieAdmissible .POmegaMinus n p e →
    Odd n → p ^ e % 4 = 3 → TwinSqAlpha p e .POmegaMinus n

theorem twinSqLive_of_rest (h : TwinSqRest p) : TwinSqLive p where
  psl hp _ hq _ hadm := twinSqAlpha_psl4 hp hq hadm
  psu := h.psu
  plus := h.plus
  minus := h.minus

theorem twinSqAlphaRows_of_rest (h : TwinSqRest p) : TwinSqAlphaRows p :=
  twinSqAlphaRows_of_live p (twinSqLive_of_rest p h)

end CFSG.ClassicalInvolution.Asc77
