module

public import CFSG.CGT.M24R.L2Inputs
public import Mathlib

public section

namespace CFSG.CGT.M24R

open CFSG.Sporadic.Th.Native

@[expose] def dT (i : Fin 3) : Table := wTab (dWord10 i)

@[expose] def thT (i : Fin 3) : Table := wTab (thetaWord10 i)

@[expose] def evT (u : Fin 3 → Table) (w : List (Fin 3)) : Table :=
  w.foldl (fun X k => compT 16 X (u k)) (idT 16)

@[expose] def dBFSq (_ : Unit := ()) :
    Array (Option (List (Fin 3))) × Array (Table × List (Fin 3)) :=
  Id.run do
    let mut arr : Array (Option (List (Fin 3))) := Array.replicate 1048576 none
    arr := arr.set! (codeOf (idT 16)) (some [])
    let mut queue : Array (Table × List (Fin 3)) := #[(idT 16, [])]
    let mut i := 0
    for _ in [0:2048] do
      if i < queue.size then
        let (X, w) := queue[i]!
        i := i + 1
        for k in List.finRange 3 do
          let Y := compT 16 X (dT k)
          let c := codeOf Y
          if (arr[c]!).isNone then
            arr := arr.set! c (some (w ++ [k]))
            queue := queue.push (Y, w ++ [k])
    return (arr, queue)

@[expose] def thWord (i : Fin 3) : List (Fin 3) := (((dBFSq ()).1)[codeOf (thT i)]!).getD []

@[expose] def Ctx8.dList (cx : Ctx8) : List ℕ := cx.codes.filter fun c => normB (cx.tab c)

@[expose] def dCheck (cx : Ctx8) : Bool :=
  (List.finRange 3).all (fun i => normB (dT i) && normB (thT i)) &&
  cx.dList.all (fun z => let Z := cx.tab z
    !(commT Z (dT 0)) || !(commT Z (dT 1)) || !(commT Z (dT 2)) || Z == idT 16) &&
  (List.finRange 3).all fun i => evT dT (thWord i) == thT i && evT thT (thWord i) == dT i

structure FCConds where
  wA : List (List (Fin 3))
  wB : List (List (Fin 3))
  wN : List (List (Fin 3))
  wP : List (List (Fin 3) × List (Fin 3))
deriving Inhabited

@[expose] def maxL (w : List (Fin 3)) : ℕ := w.foldl (fun m k => max m k.val) 0

@[expose] def fcAll (cx : Ctx8) : List FCConds :=
  let aq := dBFSq ()
  let ws := aq.2.toList.map Prod.snd
  let ps := aq.2.toList.flatMap fun xw => (List.finRange 3).map fun k =>
    (xw.2 ++ [k], ((aq.1)[codeOf (compT 16 xw.1 (dT k))]!).getD [])
  (List.range 3).map fun j =>
    { wA := ws.filter fun w => maxL w == j && cx.isTt (evT dT w)
      wB := ws.filter fun w => maxL w == j && isBt (evT dT w)
      wN := ws.filter fun w => maxL w == j && !(evT dT w == idT 16)
      wP := ps.filter fun p => max (maxL p.1) (maxL p.2) == j && evT dT p.1 == evT dT p.2 }

@[expose] def Ctx8.goodC (cx : Ctx8) (cs : FCConds) (u : Fin 3 → Table) : Bool :=
  cs.wA.all (fun w => isBt (evT u w)) && cs.wB.all (fun w => cx.isTt (evT u w)) &&
    cs.wN.all (fun w => !(evT u w == idT 16)) && cs.wP.all fun p => evT u p.1 == evT u p.2

@[expose] def Ctx8.asg (cx : Ctx8) (P : List ℕ) : Fin 3 → Table :=
  fun k => cx.tab (P.getD k.val 0)

@[expose] def Ctx8.conjEq (cx : Ctx8) (e v r : ℕ) : Bool :=
  compT 16 (cx.tab e) (cx.tab v) == compT 16 (cx.tab r) (cx.tab e)

@[expose] def Ctx8.mkReps (cx : Ctx8) (C G : List ℕ) : List ℕ :=
  G.foldl (fun reps v =>
    if reps.any fun r => C.any fun e => cx.conjEq e v r then reps else reps ++ [v]) []

@[expose] def Ctx8.fcTree (cx : Ctx8) (dl : List ℕ) (cs : List FCConds) (thc : List ℕ) :
    ℕ → List ℕ → Bool
  | 0, P => P == thc
  | fuel + 1, P =>
    let j := P.length
    let C := dl.filter fun e => P.all fun p => commT (cx.tab e) (cx.tab p)
    let G := dl.filter fun v => cx.goodC (cs.getD j default) (cx.asg (P ++ [v]))
    let t := thc.getD j 0
    let reps := cx.mkReps C (if G.contains t then t :: G else G)
    reps.all (fun r => decide (r < 1048576)) &&
      G.all (fun v => reps.any fun r => C.any fun e => cx.conjEq e v r) &&
      reps.all fun r => cx.fcTree dl cs thc fuel (P ++ [r])

@[expose] def thCodes : List ℕ := (List.finRange 3).map fun i => codeOf (thT i)

@[expose] def fcCheck (cx : Ctx8) : Bool :=
  (List.finRange 3).all (fun i => decide (codeOf (thT i) < 1048576) &&
    cx.tab (codeOf (thT i)) == thT i) &&
  cx.fcTree cx.dList (fcAll cx) thCodes 3 []

end CFSG.CGT.M24R
