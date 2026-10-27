module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child79Final
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child79Sp6Kill
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitFinal
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitMain

public section

namespace CFSG.EvenSmallLie.OmegaEight.Child79

theorem kill64_plus :
    SplitIn.Kill64 .plus :=
  N3Split.kill64_of_bridge_plus (SplitIn.bridge64_of_L9Split (Chain.l9Split .plus))

theorem kill64_minus :
    SplitIn.Kill64 .minus :=
  N3Split.kill64_of_bridge_minus (SplitIn.bridge64_of_L9Split (Chain.l9Split .minus))

theorem childO8PlusCenterless :
    ChildO8PlusCenterless :=
  childO8PlusCenterless_of_kills (SplitIn.sp6Kill .plus) kill64_plus

theorem childO8Minus :
    ChildO8Minus :=
  childO8Minus_of_kills (SplitIn.sp6Kill .minus) kill64_minus

end CFSG.EvenSmallLie.OmegaEight.Child79
