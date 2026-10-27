module

public import CFSG.CGT.L5R.L2InputsL

public section

namespace CFSG.CGT.L5R

open CFSG.Sporadic.Th.Native CFSG.CGT.M24R

@[expose] def evT2 (u : Fin 2 → Table) (w : List (Fin 2)) : Table :=
  w.foldl (fun X k => compT 16 X (u k)) (idT 16)

@[expose] def dT2 (i : Fin 2) : Table := wTab (dW10 i)

@[expose] def thT2 (i : Fin 2) : Table := wTab (thW10 i)

@[expose] def thDW : Fin 2 → List (Fin 2) :=
  ![[0], [0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0]]

@[expose] def z1DW : List (Fin 2) := [0, 1, 0, 0, 0, 1, 0, 0]

@[expose] def z2DW : List (Fin 2) := [0, 1, 0, 0, 0, 1, 0, 1, 1]

@[expose] def aDW : Fin 3 → List (Fin 2) :=
  ![[1, 0, 1, 0, 1, 0], [0, 1, 0, 1, 0, 1], [0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1]]

@[expose] def bDW : Fin 3 → List (Fin 2) :=
  ![[0, 0, 1, 0, 0, 1, 0, 0, 1], [1, 1, 0, 1, 1, 0, 1, 1, 0], [0, 1, 1, 0, 1, 1, 0, 1, 1]]

@[expose] def relDW : List (List (Fin 2) × List (Fin 2)) :=
  [([1, 1, 1, 1], []), ([0, 1, 1, 0, 0, 1, 0, 1], [1, 1, 0, 1, 1, 1, 0])]

@[expose] def sevenW : List (Fin 2) := [0, 0, 0, 0, 0, 0, 0]

@[expose] def rep2Code : ℕ := 159248

@[expose] def dListL (cx : Ctx8) : List ℕ := cx.codes.filter fun c => normAll b8List (cx.tab c)

@[expose] def dCheckL (cx : Ctx8) : Bool :=
  (List.finRange 2).all (fun i => normAll b8List (dT2 i) && normAll b8List (thT2 i)) &&
  (dListL cx).all (fun z => let Z := cx.tab z
    !(commT Z (dT2 0)) || !(commT Z (dT2 1)) || Z == idT 16) &&
  (List.finRange 2).all fun i => evT2 dT2 (thDW i) == thT2 i && evT2 thT2 (thDW i) == dT2 i

@[expose] def wCheckL (cx : Ctx8) : Bool :=
  relDW.all (fun p => evT2 dT2 p.1 == evT2 dT2 p.2) && !(dT2 0 == idT 16) &&
    evT2 dT2 sevenW == idT 16 &&
    (List.finRange 3).all (fun i => !(evT2 dT2 (aDW i) == idT 16) && cx.isTt (evT2 dT2 (aDW i))) &&
    (List.finRange 3).all (fun i => !(evT2 dT2 (bDW i) == idT 16) && isB8 (evT2 dT2 (bDW i))) &&
    conjIn (wTab nzW10) (evT2 dT2 z1DW) b8List && !(cx.isTt (evT2 dT2 z2DW)) &&
    cx.commCount (evT2 dT2 z2DW) == 4

@[expose] def conjMapD (cx : Ctx8) (dl : List ℕ) (R : Table) : Array ℕ :=
  dl.foldl (fun arr e => let E := cx.tab e
    arr.set! (codeOf (compT 16 (compT 16 (invT 16 E) R) E)) e) (Array.replicate 1048576 0)

@[expose] def viaD (cx : Ctx8) (fm : Array ℕ) (R V : Table) : Bool :=
  let e := fm[codeOf V]!
  decide (e < 1048576) && normAll b8List (cx.tab e) &&
    compT 16 (cx.tab e) V == compT 16 R (cx.tab e)

@[expose] def stage0L (cx : Ctx8) (dl : List ℕ) (R1 R2 : Table) : Bool :=
  let m1 := conjMapD cx dl R1
  let m2 := conjMapD cx dl R2
  dl.all fun v => let V := cx.tab v
    V == idT 16 || !(evT2 (fun _ => V) sevenW == idT 16) || viaD cx m1 R1 V || viaD cx m2 R2 V

@[expose] def goodL (cx : Ctx8) (fm : Array ℕ) (U : Fin 2 → Table) : Bool :=
  relDW.all (fun p => evT2 U p.1 == evT2 U p.2) &&
    (List.finRange 3).all (fun i => !(evT2 U (aDW i) == idT 16) && isB8 (evT2 U (aDW i))) &&
    (List.finRange 3).all (fun i => !(evT2 U (bDW i) == idT 16) && cx.isTt (evT2 U (bDW i))) &&
    (cx.isTt (evT2 U z1DW) || !(cx.commCount (evT2 U z1DW) == 4)) &&
    !(conjVia cx fm (betaT 0) (evT2 U z2DW))

@[expose] def stage1L (cx : Ctx8) (dl : List ℕ) (fm : Array ℕ) (R1 R2 : Table) : Bool :=
  [R1, R2].all fun R => dl.all fun v =>
    !(goodL cx fm ![R, cx.tab v]) || (R == R1 && (List.range 7).any fun k =>
      compT 16 (powT 16 k R1) (cx.tab v) == compT 16 (thT2 1) (powT 16 k R1))

@[expose] def fcCheckL (cx : Ctx8) : Bool :=
  let vc := cx.codes
  let dl := vc.filter fun c => normAll b8List (cx.tab c)
  let fm := conjMap cx vc (betaT 0)
  stage0L cx dl (thT2 0) (cx.tab rep2Code) && stage1L cx dl fm (thT2 0) (cx.tab rep2Code)

end CFSG.CGT.L5R
