module

public import CFSG.ClassicalInvolution.Asc77.AscT7ON
public import CFSG.ClassicalInvolution.Asc77.AscT7MOrth

public section

namespace CFSG.ClassicalInvolution.Asc77

set_option linter.unusedSectionVars false

variable (p : ℕ) [Fact p.Prime]


theorem twinSqOrth_proved : TwinSqOrth p where
  plus hp2 e hq n hn hadm _ := by
    rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h5
    · exact CFSG.ClassicalInvolution.G2D4Models.Twin.twinSqAlpha_d4
        CFSG.ClassicalInvolution.G2D4Models.Twin.d4FixLift_proved hp2 hq hadm
    · exact twinSqAlpha_plus_ge5 hp2 hq hadm h5
  minus hp2 e hq n hn hadm _ _ := twinSqAlpha_minus hp2 hq hadm

theorem twinSqAlphaRows_proved : TwinSqAlphaRows p :=
  twinSqAlphaRows_of_orth p (twinSqOrth_proved p)

end CFSG.ClassicalInvolution.Asc77
