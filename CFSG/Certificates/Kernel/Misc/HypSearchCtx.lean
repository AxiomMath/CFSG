module

public import CFSG.Certificates.Kernel.Misc.XiBits
public import CFSG.Certificates.Kernel.Spor.TabWords
public import Certificates.Data.Kernel.Misc.Hyp

public section

set_option exponentiation.threshold 10000

namespace CFSG.KC.Misc.Hyp

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Fischer.Native CFSG.KC.Misc.T46
  CFSG.KC.Misc.Lines CFSG.KC.Misc.Xi CFSG.KS.PK CFSG.KS.TW

structure SearchCtx (C : HCtx) (PB LB LI GI : Nat → Nat) (PL NL : Nat → List Nat) : Prop where
  P : ∀ x < 693, C.P[x]! = fl (PB x)
  PB_lt : ∀ x < 693, PB x < 2 ^ 693
  pl : ∀ x < 693, C.pl[x]! = (PL x).toArray
  mem_PL : ∀ x < 693, ∀ y, y ∈ PL x ↔ y < 693 ∧ (PB x).testBit y = true
  lam_size : C.lam.size = 1024
  lam : ∀ j < 1024, C.lam[j]! = fl (LB j)
  LB_lt : ∀ j < 1024, LB j < 2 ^ 693
  lamIdx : ∀ p < 693, C.lamIdx[p]! = filterRange (fun j => (C.lam[j]!)[p]!) 1024 []
  li : ∀ p < 693, ∀ j < 1024, (liAt LI p).testBit j = (LB j).testBit p
  gI : ∀ x < 693, TR 693 C.gI[x]! (fd 10 (GI x))
  nl : ∀ x < 693, NL x = (PL x).map fun y => y + 1024 * fd 10 (GI x) y

@[expose] def SearchMatch (v : Nat) (r : Option (List Flags)) : Prop :=
  (v = 1 → r = some []) ∧ ∀ S, v = 2 + S → r = some [fl S]

@[expose] def openPts (C : HCtx) (I X : Flags) : List Nat :=
  filterRange (fun x => I[x]! && C.pl[x]!.any fun y => !(I[y]! || X[y]!)) 693 []

@[expose] def candsAt (C : HCtx) (I X : Flags) : List (Nat × List Nat) :=
  (openPts C I X).map fun x => (x, cands C x I X)

end CFSG.KC.Misc.Hyp

end
