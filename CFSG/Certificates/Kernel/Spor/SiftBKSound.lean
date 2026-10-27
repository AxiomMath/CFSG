module

public import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import Certificates.Data.Kernel.Spor.Chain
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] noncomputable def baseImK (w m nb q BP : Nat) : Nat :=
  foldUp nb (fun t acc => Nat.lor acc (Nat.shiftLeft (pg w m q (pg w m BP t)) (Nat.mul w t)))
    (nat_lit 0)

end CFSG.KS.Raw

end
