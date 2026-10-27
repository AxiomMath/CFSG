module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuter
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorusDefs

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.HardMathSupport.Timmesfeld.CrossChar


theorem anyKindCommuteT_holds : AnyKindCommuteT :=
  fun _ _ _ _ _ S hτ _ hT _ i hq3 hQ4 z hcomm =>
    commute_rootSpan_of_commute_component_anyT S hτ hT i hq3 hQ4 z hcomm

end CFSG.HardMathSupport.Timmesfeld.LangTorus
