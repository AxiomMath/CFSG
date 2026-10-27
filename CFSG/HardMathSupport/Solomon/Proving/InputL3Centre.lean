module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma511
public import CFSG.HardMathSupport.Solomon.Proving.ExtremalCentre

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.HardMathSupport.Solomon.Proving

theorem inputL3Center_of_extremal : Lemma511Ns.InputL3Center :=
  fun _ _ _ hY => center_eq_bot_of_isExtremalType hY

end CFSG.HardMathSupport.Solomon.LocalBalance

end
