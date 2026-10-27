module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child7A
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child9A
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainShapeBLink
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.CPrimeModelFinal
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitInMain

public section

namespace CFSG.EvenSmallLie.OmegaEight.Child79


theorem childO8PlusCenterless_of_kills
    (h6 : SplitIn.Sp6Kill .plus)
    (h64 : SplitIn.Kill64 .plus) : ChildO8PlusCenterless :=
  Stage0.childO8PlusCenterless_of_shapes Child7.endgameA7 Chain.endgameB7
    CPrimeModel.endgameC'7 CPrimeModel.endgameD'7 (SplitIn.endgameC7_of h6 h64)
    (SplitIn.endgameD7_of h6 h64)

theorem childO8Minus_of_kills
    (h6 : SplitIn.Sp6Kill .minus) (h64 : SplitIn.Kill64 .minus) :
    ChildO8Minus :=
  Stage0.childO8Minus_of_shapes Child9.endgameA9 CPrimeModel.endgameC'9
    (SplitIn.endgameC9_of h6 h64)

end CFSG.EvenSmallLie.OmegaEight.Child79
