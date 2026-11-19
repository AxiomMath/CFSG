module

public import Mathlib.Data.Nat.Notation
public import Certificates.Data.CFSGNative.Th.Tables

@[expose] public section

namespace CFSG.LieType.Multipliers.U43

open CFSG.Sporadic.Th.Native

def toTable (t : Array ℕ) : Table := Array.ofFn (n := 820) fun i => UInt32.ofNat t[i.val]!

end CFSG.LieType.Multipliers.U43
