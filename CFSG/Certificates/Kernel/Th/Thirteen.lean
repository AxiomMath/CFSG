module

public import CFSG.Certificates.Kernel.Th.Expr
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.ThThirteenInputs

public section

namespace CFSG.KC.Th.Thirteen

open CFSG.KC.Th.Expr CFSG.HardMathSupport.Dickson.Sec6.I1431.ThThirteenNative

@[expose] noncomputable def strictB (y : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (f 0) (fun n _ => f (Nat.succ n)) y

theorem strictB_eq (y : Nat) (f : Nat → Bool) : strictB y f = f y := by
  cases y <;> rfl

@[expose] noncomputable def letK (P Q Q2 : Nat) (l : Int) : Nat :=
  if l = 1 ∨ l = -1 then P else if l = 2 then Q else Q2

@[expose] noncomputable def wordK (k : K) (P Q Q2 : Nat) (w : List Int) : Nat :=
  w.foldl (fun acc l => k.mul acc (letK P Q Q2 l)) k.ONE

@[expose] noncomputable def powK (k : K) (P e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) k.ONE (fun _ acc => k.mul acc P) e

@[expose] noncomputable def th13KW (k : K) (yw gw : List Int) : Bool :=
  strictB (k.mul k.SB k.SB) fun B2 =>
  strictB (wordK k k.SA k.SB B2 (CFSG.Sporadic.Th.Native.xWord ())) fun X =>
  strictB (wordK k k.SA k.SB B2 (CFSG.Sporadic.Th.Native.yWord ())) fun Y0 =>
  strictB (k.mul Y0 Y0) fun Y2 =>
  strictB (wordK k X Y0 Y2 yw) fun Y =>
  strictB (wordK k X Y0 Y2 gw) fun G =>
  Nat.beq (powK k Y 13) k.ONE && !Nat.beq Y k.ONE && Nat.beq (k.mul Y G) (k.mul G (powK k Y 2))

@[expose] noncomputable def th13K (k : K) : Bool := th13KW k y13Word g13Word

end CFSG.KC.Th.Thirteen

end
