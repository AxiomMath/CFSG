module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoFusionBase
import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotMatK

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6

open CFSG.StandardType.E6TwoMat CFSG.StandardType.E6TwoPilot CFSG.StandardType.E6TwoMatK

@[expose] def cwU3 : List ℕ :=
  [32, 64, 11, 63, 69, 20, 76, 34, 10, 21, 14, 35, 7, 34, 75, 58, 74, 77, 32, 21, 37, 16, 15, 29]

theorem fuseU3 :
    wordsAgree (cwU3 ++ xWord 1 1 ![0, 0, 1, 0]) (eWord ![2, 1, 1, 0] ++ cwU3) = true :=
  wordsAgree_of_K (by decide +kernel)

@[expose] def cwU4 : List ℕ :=
  [22, 20, 64, 56, 64, 72, 54, 23, 65, 71, 16, 58, 8, 72, 27, 25, 19, 28, 40]

theorem fuseU4 :
    wordsAgree (cwU4 ++ xWord 1 1 ![0, 0, 2, 0]) (eWord ![1, 2, 1, 0] ++ cwU4) = true :=
  wordsAgree_of_K (by decide +kernel)

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6
