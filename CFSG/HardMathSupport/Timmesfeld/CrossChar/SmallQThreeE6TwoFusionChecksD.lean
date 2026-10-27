module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoFusionBase
import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotMatK

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6

open CFSG.StandardType.E6TwoMat CFSG.StandardType.E6TwoPilot CFSG.StandardType.E6TwoMatK

@[expose] def cwV0 : List ℕ :=
  [57, 8, 7, 31, 39, 67, 70, 10, 7, 52, 57, 45, 51, 44, 31, 19, 17, 16, 38, 15, 56]

theorem fuseV0 :
    wordsAgree (cwV0 ++ xWord 2 1 ![0, 0, 0, 0]) (eWord ![1, 0, 2, 1] ++ cwV0) = true :=
  wordsAgree_of_K (by decide +kernel)

@[expose] def cwV1 : List ℕ :=
  [43, 24, 52, 45, 44, 68, 50, 51, 41, 62, 57, 24, 72, 43, 66, 70, 19, 17, 16, 38, 15, 56]

theorem fuseV1 :
    wordsAgree (cwV1 ++ xWord 2 1 ![0, 1, 2, 0]) (eWord ![0, 2, 1, 1] ++ cwV1) = true :=
  wordsAgree_of_K (by decide +kernel)

@[expose] def cwV2 : List ℕ :=
  [57, 42, 66, 20, 39, 71, 34, 52, 42, 16, 68, 67, 73, 72, 66, 19, 17, 16, 38, 15, 56]

theorem fuseV2 :
    wordsAgree (cwV2 ++ xWord 2 1 ![1, 0, 2, 0]) (eWord ![0, 2, 2, 1] ++ cwV2) = true :=
  wordsAgree_of_K (by decide +kernel)

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6
