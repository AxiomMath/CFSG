module

public import Certificates.Data.CFSGNative.HS.SmallF2

public section

namespace CFSG.GF2Type.Smith1979.W4C2

namespace LocalTest

open CFSG.Sporadic.SmallF2.Native

structure El where
  G : Array Nat
  H : Array Nat
  s : Bool

@[expose] def eqN (a b : Nat) : Bool := a % 16 == b % 16

@[expose] def eqV (u v : Nat × Nat) : Bool := eqN u.1 v.1 && eqN u.2 v.2

@[expose] def eqR (R R' : Array Nat) : Bool :=
  (List.range 4).all fun i => eqN (R[i]?.getD 0) (R'[i]?.getD 0)

@[expose] def eqE (E E' : El) : Bool := eqR E.G E'.G && eqR E.H E'.H && E.s == E'.s

@[expose] def idE : El := ⟨idRows 4, idRows 4, false⟩

@[expose] def mulE (E E' : El) : El :=
  if E.s then ⟨mulRows 4 E'.H E.G, mulRows 4 E'.G E.H, !E'.s⟩
  else ⟨mulRows 4 E'.G E.G, mulRows 4 E'.H E.H, E'.s⟩

@[expose] def invE (E : El) : El :=
  if E.s then ⟨transposeRows 4 E.G, transposeRows 4 E.H, true⟩
  else ⟨transposeRows 4 E.H, transposeRows 4 E.G, false⟩

@[expose] def conj (F E : El) : El := mulE (mulE F E) (invE F)

@[expose] def commuteE (E X : El) : Bool := eqE (mulE E X) (mulE X E)

@[expose] def appE (E : El) (v : Nat × Nat) : Nat × Nat :=
  if E.s then (vecMulN 4 E.G v.2, vecMulN 4 E.H v.1) else (vecMulN 4 E.G v.1, vecMulN 4 E.H v.2)

@[expose] def validE (E : El) : Bool := eqR (mulRows 4 E.G (transposeRows 4 E.H)) (idRows 4)

@[expose] def allRows : List (Array Nat) :=
  (List.range 65536).map fun n => #[n % 16, n / 16 % 16, n / 256 % 16, n / 4096]

@[expose] def injRows (R : Array Nat) : Bool :=
  (List.range 15).all fun i => vecMulN 4 R (i + 1) % 16 != 0

@[expose] def invRows (R : Array Nat) : Array Nat :=
  Array.ofFn (n := 4) fun j =>
    ((List.range 16).find? fun x => vecMulN 4 R x % 16 == 1 <<< j.val).getD 0

@[expose] def dualRows (R : Array Nat) : Array Nat := transposeRows 4 (invRows R)

@[expose] def Hlist (_ : Unit := ()) : List El :=
  (allRows.filter injRows).flatMap fun R =>
    let D := dualRows R
    [⟨R, D, false⟩, ⟨R, D, true⟩]

@[expose] def bN : Nat × Nat := (1, 0)

@[expose] def bM : Nat × Nat := (1, 2)

@[expose] def dot4 (x y : Nat) : Bool :=
  (x.testBit 0 && y.testBit 0) ^^ (x.testBit 1 && y.testBit 1) ^^ (x.testBit 2 && y.testBit 2) ^^
    (x.testBit 3 && y.testBit 3)

@[expose] def polarB (b v : Nat × Nat) : Bool := dot4 b.1 v.2 ^^ dot4 v.1 b.2

@[expose] def perp (b : Nat × Nat) : List (Nat × Nat) :=
  ((List.range 16).flatMap fun x => (List.range 16).map fun y => (x, y)).filter fun v =>
    !(polarB b v)

@[expose] def xorV (u v : Nat × Nat) : Nat × Nat := (u.1 ^^^ v.1, u.2 ^^^ v.2)

@[expose] def orbOK (H : List El) : Bool :=
  (List.range 256).all fun n =>
    let v := (n % 16, n / 16)
    n == 0 || dot4 v.1 v.2 ||
      H.any fun E => eqV (appE E (if v.1 == 0 || v.2 == 0 then bN else bM)) v

@[expose] def isComm (P : List El) (E : El) : Bool :=
  eqE (mulE E E) idE && P.all fun F => commuteE E (conj F E)

@[expose] def candOK (P Cl : List El) : Bool :=
  P.all fun E => !(eqE (mulE E E) idE) || Cl.any (eqE E) ||
    P.any fun F => !commuteE E (conj F E)

@[expose] def E1 : El := ⟨#[1, 3, 4, 8], #[3, 2, 4, 8], false⟩

@[expose] def stabL (H : List El) (b : Nat × Nat) : List El :=
  H.filter fun E => eqV (appE E b) b

@[expose] def chkN (H : List El) : Bool :=
  let P := stabL H bN
  let U := P.filter (isComm P)
  candOK P U && U.all fun E => eqE E idE || P.any fun F => eqE (conj F E) E1

@[expose] def ws4 : List (Nat × Nat) := [(1, 2), (0, 2), (4, 8), (8, 4)]

@[expose] def chkM (H : List El) : Bool :=
  let P := stabL H bM
  let Cl := P.filter (isComm P)
  let Kl := Cl.filter (·.s == false)
  candOK P Cl && Cl.length == 16 &&
    Cl.all (fun c => eqE (mulE c c) idE &&
      Cl.all fun c' => Cl.any (eqE (mulE c c')) && commuteE c c') &&
    P.all (fun F => Cl.all fun c => Cl.any (eqE (conj F c))) &&
    Kl.all (fun k => P.any fun p => Cl.any fun c => eqE (mulE (conj p c) c) k) &&
    ws4.all (fun w => Kl.any fun k => (perp bM).any fun v => eqV (xorV (appE k v) v) w) &&
    Kl.any fun k => !(eqE k idE) && ws4.all fun w => eqV (appE k w) w

end LocalTest

@[expose] def chk : Bool :=
  let H := LocalTest.Hlist ()
  H.all LocalTest.validE && LocalTest.orbOK H && LocalTest.chkN H && LocalTest.chkM H

end CFSG.GF2Type.Smith1979.W4C2
