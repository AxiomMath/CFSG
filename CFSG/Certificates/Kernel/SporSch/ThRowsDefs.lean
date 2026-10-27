
module

public import CFSG.Sporadic.ThSchreier.Text

public section

namespace CFSG.KS.SporSch

open CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier

@[expose] def rowsV (R : Nat → Nat) : Array V4 := Array.ofFn (n := 248) fun i => v4OfNat (R i.val)

end CFSG.KS.SporSch

end
