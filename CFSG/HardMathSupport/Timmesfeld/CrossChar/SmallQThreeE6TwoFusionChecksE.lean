module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoFusionBase
import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotMatK

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6

open CFSG.StandardType.E6TwoMat CFSG.StandardType.E6TwoPilot CFSG.StandardType.E6TwoMatK

@[expose] def cwV3 : List ℕ :=
  [74, 77, 55, 53, 32, 64, 11, 49, 55, 44, 43, 7, 58, 45, 27, 38, 9, 25]

theorem fuseV3 :
    wordsAgree (cwV3 ++ xWord 2 1 ![0, 0, 1, 0]) (eWord ![2, 2, 2, 0] ++ cwV3) = true :=
  wordsAgree_of_K (by decide +kernel)

@[expose] def cwV4 : List ℕ :=
  [74, 77, 55, 53, 32, 64, 11, 49, 55, 44, 43, 7, 58, 45, 27, 38, 9, 25, 7, 14, 7, 8, 16, 8, 10,
    20, 10, 49, 56, 49]

theorem fuseV4 :
    wordsAgree (cwV4 ++ xWord 2 1 ![1, 1, 0, 1]) (eWord ![2, 2, 2, 0] ++ cwV4) = true :=
  wordsAgree_of_K (by decide +kernel)

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6
