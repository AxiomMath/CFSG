module

public import CFSG.Sporadic.Schreier.LyCheckCover

public section

namespace CFSG.ComponentClassification.UnbalancedAltSeven.Native

open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.Ly.Native CFSG.Sporadic.He.Native

set_option compiler.extract_closed false

@[expose] def liftSquareCheck (_ : Unit) : Bool :=
  let cs := cStarArr (powM 5 111 matB 4)
  mulM 5 111 (pairAt cs 8).1 (pairAt cs 8).1 == matA

end CFSG.ComponentClassification.UnbalancedAltSeven.Native
