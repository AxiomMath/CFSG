module

public import Certificates.Data.CFSGNative.Th.Tables
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.LocalComp.Tits

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.Th.Native

@[expose] noncomputable def tabP (N P : Nat) : Table :=
  Array.ofFn (n := N) fun i => UInt32.ofNat (pg 11 (mask 11) P i.val)

end CFSG.KC.LocalComp.Tits

end
