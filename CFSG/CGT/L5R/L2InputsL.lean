module

public import CFSG.CGT.M24R.L2InputsD

public section

namespace CFSG.CGT.L5R

open CFSG.Sporadic.Th.Native CFSG.CGT.M24R

@[expose] def betaW10 : Fin 3 → List (Fin 10 × Bool) :=
  ![[(0, true), (1, true), (2, true), (4, false), (2, true), (3, false), (0, true), (5, false),
     (8, true), (9, true)],
    [(0, true), (2, true), (1, true), (5, true), (0, true), (2, true), (4, true), (3, true),
     (7, true), (8, true), (9, true)],
    [(0, true), (1, true), (2, true), (3, true), (0, true), (4, true), (3, false), (5, true),
     (1, false), (7, true), (8, true)]]

@[expose] def gammaW10 : List (Fin 10 × Bool) :=
  [(0, true), (1, true), (2, true), (5, false), (2, true), (4, false), (0, true), (3, false),
   (6, true)]

@[expose] def dW10 : Fin 2 → List (Fin 10 × Bool) :=
  ![[(0, true), (1, true), (2, true), (5, false), (4, true)],
    [(5, true), (4, true), (3, true), (0, false), (8, true)]]

@[expose] def thW10 : Fin 2 → List (Fin 10 × Bool) :=
  ![[(0, true), (1, true), (2, true), (5, false), (4, true)],
    [(3, true), (1, true), (4, false), (2, true), (8, true)]]

@[expose] def nzW10 : List (Fin 10 × Bool) := [(3, false)]

@[expose] def betaT (i : Fin 3) : Table := wTab (betaW10 i)

@[expose] def gamT : Table := wTab gammaW10

@[expose] def eightT (P Q R : Table) : List Table :=
  [idT 16, P, Q, compT 16 P Q, R, compT 16 P R, compT 16 Q R, compT 16 (compT 16 P Q) R]

@[expose] def b8List : List Table := eightT (betaT 0) (betaT 1) (betaT 2)

@[expose] def isB8 (X : Table) : Bool := b8List.contains X

@[expose] def normAll (L : List Table) (X : Table) : Bool :=
  L.all fun P => conjIn X P L && conjInR X P L

@[expose] def bCheckL (cx : Ctx8) : Bool :=
  decide b8List.Nodup && b8List.all (fun X => compT 16 X X == idT 16) &&
    b8List.all (fun X => b8List.all fun Y => b8List.contains (compT 16 X Y)) &&
    b8List.tail.all (fun X => !(cx.isTt X)) && !(cx.isTt gamT)

@[expose] def conjMap (cx : Ctx8) (vc : List ℕ) (P : Table) : Array ℕ :=
  vc.foldl (fun arr c => let N := cx.tab c
    arr.set! (codeOf (compT 16 (compT 16 N P) (invT 16 N))) c) (Array.replicate 1048576 0)

@[expose] def conjVia (cx : Ctx8) (fm : Array ℕ) (P X : Table) : Bool :=
  let n := fm[codeOf X]!
  decide (n < 1048576) && compT 16 (cx.tab n) P == compT 16 X (cx.tab n)

@[expose] def faCheckL (cx : Ctx8) : Bool :=
  let vc := cx.codes
  let fb := conjMap cx vc (betaT 0)
  let fg := conjMap cx vc gamT
  vc.all fun c =>
    let X := cx.tab c
    !(compT 16 X X == idT 16) || cx.isTt X || !(cx.commCount X == 8) ||
      conjVia cx fb (betaT 0) X || conjVia cx fg gamT X

@[expose] def candL (cx : Ctx8) (P X : Table) : Bool :=
  compT 16 X X == idT 16 && commT X P && !(cx.isTt X) && !(X == P) &&
    !(cx.isTt (compT 16 P X)) && (List.range 16).all fun k => commT cx.tt[k]! X == commT cx.tt[k]! P

@[expose] def pairPre (cx : Ctx8) (P X Y : Table) : Bool :=
  commT X Y && !(Y == P) && !(Y == X) && !(Y == compT 16 P X) && candL cx P (compT 16 X Y) &&
    candL cx P (compT 16 (compT 16 P X) Y)

@[expose] def refL (L : List Table) (X Y Z : Table) : Bool := !(conjIn Z X L) || !(conjIn Z Y L)

@[expose] def fbCheckL (cx : Ctx8) (P : Table) (allowB : Bool) : Bool :=
  let vc := cx.codes
  let cands := vc.filter fun c => candL cx P (cx.tab c)
  let cent := vc.filter fun y => commT (cx.tab y) P
  cands.all fun c => cands.all fun c' =>
    let X := cx.tab c
    let Y := cx.tab c'
    !(pairPre cx P X Y) || (decide (eightT P X Y).Nodup &&
      ((allowB && isB8 X && isB8 Y) || cent.any fun y => refL (eightT P X Y) X Y (cx.tab y)))

end CFSG.CGT.L5R
