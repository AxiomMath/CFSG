module

public import CFSG.Assembly.E6FourCentData

public section

namespace CFSG.Assembly.E6FourCentChk

@[expose] def M72 : Nat := 4722366482869645213695

@[expose] def expand (A : Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | n + 1, fr, acc =>
    bif Nat.beq fr 0 then acc else
      expand A n (Nat.xor fr (Nat.shiftLeft 1 (Nat.log2 fr)))
        (Nat.lor acc (Nat.land (Nat.shiftRight A (Nat.mul 72 (Nat.log2 fr))) M72))

@[expose] def bfs (A S : Nat) : Nat → Nat → Nat → Nat
  | 0, vis, _ => vis
  | n + 1, vis, fr =>
    bif Nat.beq fr 0 then vis else
      let nx := Nat.land (Nat.land (expand A 72 fr 0) S) (Nat.xor vis M72)
      bfs A S n (Nat.lor vis nx) nx

@[expose] def compOf (A S k : Nat) : Nat :=
  bfs A S 12 (Nat.shiftLeft 1 k) (Nat.shiftLeft 1 k)

@[expose] def closedOK (A S c : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.land (expand A 72 c 0) S) (Nat.xor c M72)) 0

@[expose] def mapMaskP (P : Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | n + 1, m, acc =>
    bif Nat.beq m 0 then acc else
      mapMaskP P n (Nat.xor m (Nat.shiftLeft 1 (Nat.log2 m)))
        (Nat.lor acc (Nat.shiftLeft 1
          (Nat.land (Nat.shiftRight P (Nat.mul 7 (Nat.log2 m))) 127)))

@[expose] def popc (m : Nat) : Nat :=
  (List.range 72).foldl (fun a k => Nat.add a (Nat.land (Nat.shiftRight m k) 1)) 0

@[expose] def hasFive (R : Nat) : List Nat → Nat → Bool
  | [], c => Nat.ble 5 c
  | m :: ms, c =>
    bif Nat.ble 5 c then true
    else hasFive R ms (bif Nat.beq (Nat.land R m) R then Nat.add c 1 else c)

@[expose] def dotI (x y : List Int) : Int := (List.zipWith (· * ·) x y).foldl (· + ·) 0

@[expose] def mulVecI (A : List (List Int)) (y : List Int) : List Int := A.map fun r => dotI r y

@[expose] def iformI (x y : List Int) : Int := dotI x (mulVecI cartLit y)

@[expose] def rt (k : Nat) : List Int := rtsLit.getD k []

@[expose] def rootsOf (c : Nat) : List (List Int) :=
  ((List.range 72).filter fun k => Nat.testBit c k).map rt

@[expose] def vsub (x y : List Int) : List Int := List.zipWith (· - ·) x y

@[expose] def wAct (bs : List (List Int)) (x : List Int) : List Int :=
  bs.foldl (fun y b => vsub y (b.map fun t => iformI y b * t)) x

@[expose] def dualOK (gs ds : List (List Int)) : Bool :=
  (List.range gs.length).all fun i => (List.range ds.length).all fun j =>
    bif Nat.beq i j then dotI (gs.getD i []) (ds.getD j []) != 0
    else dotI (gs.getD i []) (ds.getD j []) == 0

@[expose] def a5Valid (e : A5Cert) : Bool :=
  let rs := rootsOf e.c
  Nat.testBit e.c e.b1 && Nat.testBit e.c e.b2 && Nat.testBit e.c e.b3 &&
  Nat.testBit e.c e.g1 && Nat.testBit e.c e.g2 && Nat.testBit e.c e.g3 &&
  Nat.testBit e.c e.g4 && Nat.testBit e.c e.g5 &&
  iformI (rt e.b1) (rt e.b2) == 0 && iformI (rt e.b1) (rt e.b3) == 0 &&
  iformI (rt e.b2) (rt e.b3) == 0 &&
  rs.all (fun g => mulVecI matLit g == wAct [rt e.b1, rt e.b2, rt e.b3] g) &&
  dualOK [rt e.g1, rt e.g2, rt e.g3, rt e.g4, rt e.g5] [e.d1, e.d2, e.d3, e.d4, e.d5] &&
  e.u.any (fun z => z != 0) && rs.all (fun g => dotI g e.u == 0)

@[expose] def d4Valid (e : D4Cert) : Bool :=
  let rs := rootsOf e.c
  let U := List.zipWith (· + ·) (rt e.b1) (rt e.b2)
  Nat.testBit e.c e.b1 && Nat.testBit e.c e.b2 &&
  Nat.testBit e.c e.g1 && Nat.testBit e.c e.g2 && Nat.testBit e.c e.g3 && Nat.testBit e.c e.g4 &&
  iformI (rt e.b1) (rt e.b2) == 0 &&
  rs.all (fun g => iformI U g % 2 == 0) &&
  (vsub (mulVecI matLit U) U).any (fun z => z % 2 != 0) &&
  dualOK [rt e.g1, rt e.g2, rt e.g3, rt e.g4] [e.d1, e.d2, e.d3, e.d4] &&
  rs.all (fun g => dotI g e.u1 == 0 && dotI g e.u2 == 0) &&
  (e.u1.getD e.p 0 * e.u2.getD e.q 0 - e.u1.getD e.q 0 * e.u2.getD e.p 0) != 0

@[expose] def typedOK (c m : Nat) : Bool :=
  Nat.beq m c &&
    ((Nat.beq (popc c) 30 && a5Tab.any fun e => Nat.beq e.c c && a5Valid e) ||
     (Nat.beq (popc c) 24 && d4Tab.any fun e => Nat.beq e.c c && d4Valid e))

@[expose] def rowOK (S c : Nat) : Bool :=
  let m := mapMaskP permLit 72 c 0
  closedOK adjLit S c && (hasFive (Nat.lor c m) sigsLit 0 || typedOK c m)

@[expose] def rowsOK (S : Nat) : Nat → Nat → Bool
  | 0, rem => Nat.beq rem 0
  | n + 1, rem =>
    bif Nat.beq rem 0 then true else
      let c := compOf adjLit S (Nat.log2 rem)
      rowOK S c && rowsOK S n (Nat.land rem (Nat.xor c M72))

@[expose] def vecOK (S : Nat) : Bool := rowsOK S 72 S

@[expose] def tableOK (_ : Unit := ()) : Bool := sigsLit.all vecOK

theorem e6FourTable_ok : tableOK () = true := by decide +kernel

end CFSG.Assembly.E6FourCentChk

end
