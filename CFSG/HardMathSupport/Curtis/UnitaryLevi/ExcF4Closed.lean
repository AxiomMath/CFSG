module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcF4Cell
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcF4Cent

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Malle.E27Lie (InnerLeaf)
open CFSG.HardMathSupport.Curtis.Coordinator.ExcLeaf (IdxExc)

theorem monomialThreeCentralizerBoundF4
    : MonomialThreeCentralizerBoundF4 :=
  fun K _ _ h3 n hn => eightyOne_dvd_centralizer_F4 K h3 n hn

theorem innerLeaf_F4_one
    : InnerLeaf (IdxExc .F4 1) :=
  innerLeaf_F4_one_of_monomialBound monomialThreeCentralizerBoundF4

end CFSG.HardMathSupport.Curtis.UnitaryLevi

end
