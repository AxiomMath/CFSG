module

public import Certificates.Data.CFSGNative.SectionRank.Elem3
public import Mathlib.Data.Nat.Notation

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.SectionRank.Native

structure NatOps (N : Type) where
  one : N
  mul : N → N → N
  pow : N → ℕ → N
  eqb : N → N → Bool
  neb : N → N → Bool

set_option compiler.extract_closed false

end CFSG.HardMathSupport.Dickson.I271
