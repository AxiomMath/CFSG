module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
public import CFSG.Sporadic.Schreier.TitsOrbit
public import CFSG.Certificates.NativeInvariantMerge
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
public meta import CFSG.Sporadic.Schreier.TitsOrbit
public meta import CFSG.Certificates.NativeInvariantMerge
public meta import CFSG.Sporadic.Schreier.TitsBasic
public import CFSG.Sporadic.Schreier.TitsBasic

public section

namespace CFSG.ComponentClassification.AS81.MinusLines

open CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2.Native CFSG.Certificates
open CFSG.Certificates.Native CFSG.Sporadic.Schreier.Tits

@[expose] def omega1Gens : Array (Array ℕ) :=
  Array.ofFn (n := 8) fun i => copy0Arr genArrs[i.val]!

@[expose] def thirdPt (a b : ℕ) : ℕ := nsIdx[nsArr[a]! ^^^ nsArr[b]!]!

@[expose] def lineHead (a b : ℕ) : Bool :=
  decide (a < b) && bNat nsArr[a]! nsArr[b]! && decide (b < thirdPt a b)

@[expose] def lineList : List (ℕ × ℕ × ℕ) :=
  (List.range 120).flatMap fun a =>
    ((List.range 120).filter fun b => lineHead a b).map fun b => (a, b, thirdPt a b)

@[expose] def lineArr : Array (ℕ × ℕ × ℕ) := lineList.toArray

@[expose] def pairLine : Array ℕ := Id.run do
  let mut T : Array ℕ := Array.replicate 14400 0
  for t in [0:lineArr.size] do
    let s := lineArr[t]!
    T := T.set! (120 * s.1 + s.2.1) t
    T := T.set! (120 * s.2.1 + s.1) t
    T := T.set! (120 * s.1 + s.2.2) t
    T := T.set! (120 * s.2.2 + s.1) t
    T := T.set! (120 * s.2.1 + s.2.2) t
    T := T.set! (120 * s.2.2 + s.2.1) t
  return T

@[expose] def lineImage (g : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 1120) fun t =>
    let s := lineArr[t.val]!
    pairLine[120 * g[s.1]! + g[s.2.1]!]!

@[expose] def lineGens : Array (Array ℕ) := omega1Gens.map lineImage

@[expose] def onLine (s : ℕ × ℕ × ℕ) (x : ℕ) : Bool := x == s.1 || x == s.2.1 || x == s.2.2

@[expose] def lineH0Words : List (List ℤ) := [[6], [7], [-1, 2], [-4, -8, 3, 5, 3, 4]]

@[expose] def lineH0Arrs : Array (Array ℕ) :=
  (lineH0Words.map fun w => wordArr 1120 lineGens w).toArray

@[expose] def lineH0Reps : Array ℕ := #[0, 1, 28, 32, 58]

@[expose] def lineH0Forest : Array ℕ × Array ℕ × Array ℕ × Array ℕ :=
  orbitForest 1120 lineH0Arrs lineH0Reps

@[expose] def lineRoot (parent : Array ℕ) (x : ℕ) : ℕ := Id.run do
  let mut r := x
  for _ in [0:parent.size] do
    let p := parent[r]!
    if p == r then break
    r := p
  return r

@[expose] def lineMergeSearch (n : ℕ) (G : Array (Array ℕ)) (b x : ℕ) : List (ℕ × ℕ × ℕ) :=
  Id.run do
    let mut parent : Array ℕ := Array.ofFn (n := n) fun i => i.val
    let mut sz : Array ℕ := Array.replicate n 1
    let mut queue : Array (ℕ × ℕ) := #[]
    let mut out : Array (ℕ × ℕ × ℕ) := #[]
    let rb := lineRoot parent b
    let rx := lineRoot parent x
    if rb != rx then
      parent := parent.set! rx rb
      sz := sz.set! rb (sz[rb]! + sz[rx]!)
      queue := queue.push (b, x)
    let mut head := 0
    for _ in [0:2 * n] do
      if head < queue.size then
        let (u, v) := queue[head]!
        head := head + 1
        for i in [0:G.size] do
          let a := (G[i]!)[u]!
          let c := (G[i]!)[v]!
          let ra := lineRoot parent a
          let rc := lineRoot parent c
          if ra != rc then
            if sz[ra]! < sz[rc]! then
              parent := parent.set! ra rc
              sz := sz.set! rc (sz[rc]! + sz[ra]!)
            else
              parent := parent.set! rc ra
              sz := sz.set! ra (sz[ra]! + sz[rc]!)
            out := out.push (i, u, v)
            queue := queue.push (a, c)
    return out.toList

@[expose] def lineMerge (l : ℕ) : List (Fin 8 × Fin 1120 × Fin 1120) :=
  (lineMergeSearch 1120 lineGens 0 lineH0Reps[l + 1]!).map fun m =>
    (finPt 8 m.1, finPt 1120 m.2.1, finPt 1120 m.2.2)

@[expose] def lineCheck : Bool :=
  allLt 1120 (fun t =>
    decide (lineArr[t]!.1 < lineArr[t]!.2.1) && decide (lineArr[t]!.2.1 < lineArr[t]!.2.2) &&
      decide (lineArr[t]!.2.2 < 120) && pairLine[120 * lineArr[t]!.1 + lineArr[t]!.2.1]! == t) &&
  allLt 120 fun a => allLt 120 fun b =>
    !(a != b && bNat nsArr[a]! nsArr[b]!) || (decide (pairLine[120 * a + b]! < 1120) &&
      onLine lineArr[pairLine[120 * a + b]!]! a && onLine lineArr[pairLine[120 * a + b]!]! b &&
      onLine lineArr[pairLine[120 * a + b]!]! (thirdPt a b))

@[expose] def lineGensCheck : Bool :=
  allPermsOK 1120 lineGens &&
    allLt 8 fun i => allLt 1120 fun t =>
      onLine lineArr[(lineGens[i]!)[t]!]! (omega1Gens[i]!)[lineArr[t]!.1]! &&
        onLine lineArr[(lineGens[i]!)[t]!]! (omega1Gens[i]!)[lineArr[t]!.2.1]! &&
        onLine lineArr[(lineGens[i]!)[t]!]! (omega1Gens[i]!)[lineArr[t]!.2.2]!

@[expose] def lineTransCheck : Bool := forestOK 1120 lineGens #[0]

@[expose] def lineH0Check : Bool :=
  lineH0Words.all (lettersOK 8) && allLt 4 (fun j => (lineH0Arrs[j]!)[0]! == 0) &&
    orbitLabelOK 1120 lineH0Arrs 5 lineH0Forest.1 lineH0Reps lineH0Forest.2.1 lineH0Forest.2.2.1
      lineH0Forest.2.2.2

@[expose] def lineMergeCheck : Bool :=
  allLt 4 fun l => mergeOK 1120 lineGens 0 lineH0Reps[l + 1]! (mergeVals (lineMerge l))

end CFSG.ComponentClassification.AS81.MinusLines
