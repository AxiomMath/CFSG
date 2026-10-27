module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoFusionBase
import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotMatK

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6

open CFSG.StandardType.E6TwoMat CFSG.StandardType.E6TwoPilot CFSG.StandardType.E6TwoMatK

@[expose] def cwU0 : List ℕ :=
  [57, 8, 7, 31, 39, 67, 70, 10, 7, 52, 57, 45, 51, 44, 31, 19, 17, 16, 38, 15, 56]

theorem fuseU0 :
    wordsAgree (cwU0 ++ xWord 1 1 ![0, 0, 0, 0]) (eWord ![1, 0, 2, 2] ++ cwU0) = true :=
  wordsAgree_of_K (by decide +kernel)

@[expose] def cwU1 : List ℕ :=
  [57, 42, 66, 20, 39, 71, 34, 52, 42, 16, 68, 67, 73, 72, 66, 19, 17, 16, 38, 15, 56]

theorem fuseU1 :
    wordsAgree (cwU1 ++ xWord 1 1 ![1, 0, 2, 0]) (eWord ![0, 2, 2, 2] ++ cwU1) = true :=
  wordsAgree_of_K (by decide +kernel)

@[expose] def cwU2 : List ℕ :=
  [43, 24, 52, 45, 44, 68, 50, 51, 41, 62, 57, 24, 72, 43, 66, 70, 19, 17, 16, 38, 15, 56]

theorem fuseU2 :
    wordsAgree (cwU2 ++ xWord 1 1 ![0, 1, 2, 0]) (eWord ![0, 2, 1, 2] ++ cwU2) = true :=
  wordsAgree_of_K (by decide +kernel)

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6
