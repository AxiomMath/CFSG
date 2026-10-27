module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoFusionBase
import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotMatK

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6

open CFSG.StandardType.E6TwoMat CFSG.StandardType.E6TwoPilot CFSG.StandardType.E6TwoMatK

@[expose] def cwT0 : List ℕ :=
  [31, 51, 50, 8, 45, 35, 67, 66, 35, 39, 70, 68, 57, 70, 35, 57, 62, 71, 50]

theorem fuseT0 :
    wordsAgree (cwT0 ++ xWord 0 1 ![0, 0, 0, 0]) (eWord ![0, 1, 2, 0] ++ cwT0) = true :=
  wordsAgree_of_K (by decide +kernel)

@[expose] def cwT1 : List ℕ :=
  [31, 51, 50, 8, 45, 35, 67, 66, 35, 39, 70, 68, 57, 70, 35, 57, 62, 71, 50]

theorem fuseT1 :
    wordsAgree (cwT1 ++ xWord 0 1 ![0, 0, 0, 1]) (eWord ![0, 1, 2, 1] ++ cwT1) = true :=
  wordsAgree_of_K (by decide +kernel)

@[expose] def cwT2 : List ℕ :=
  [31, 51, 50, 8, 45, 35, 67, 66, 35, 39, 70, 68, 57, 70, 35, 57, 62, 71, 50]

theorem fuseT2 :
    wordsAgree (cwT2 ++ xWord 0 1 ![0, 0, 0, 2]) (eWord ![0, 1, 2, 2] ++ cwT2) = true :=
  wordsAgree_of_K (by decide +kernel)

@[expose] def cwS0 : List ℕ :=
  [19, 17, 16, 38, 15, 56]

theorem fuseS0 :
    wordsAgree (cwS0 ++ xWord 1 0 ![0, 0, 0, 0]) (eWord ![0, 0, 0, 2] ++ cwS0) = true :=
  wordsAgree_of_K (by decide +kernel)

@[expose] def cwS1 : List ℕ :=
  [19, 17, 16, 38, 15, 56]

theorem fuseS1 :
    wordsAgree (cwS1 ++ xWord 1 0 ![0, 1, 2, 0]) (eWord ![0, 2, 2, 2] ++ cwS1) = true :=
  wordsAgree_of_K (by decide +kernel)

@[expose] def cwS2 : List ℕ :=
  [19, 17, 16, 38, 15, 56]

theorem fuseS2 :
    wordsAgree (cwS2 ++ xWord 1 0 ![0, 2, 1, 0]) (eWord ![0, 1, 1, 2] ++ cwS2) = true :=
  wordsAgree_of_K (by decide +kernel)

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6
