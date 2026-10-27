module

public import CFSG.CGT.M24R.L2Data
public import CFSG.CGT.M24R.RelData

public section

namespace CFSG.CGT.M24R

open CFSG.Sporadic.Th.Native

@[expose] def xLetters : List (Fin 10 × Bool) :=
  (List.finRange 6).flatMap fun i => [(⟨i.val, by omega⟩, true), (⟨i.val, by omega⟩, false)]

@[expose] def lBFS (_ : Unit := ()) : Array (Option (List (Fin 10 × Bool))) := Id.run do
  let mut arr : Array (Option (List (Fin 10 × Bool))) := Array.replicate 65536 none
  arr := arr.set! (codeOf (idT 16) / 16) (some [])
  let mut queue : Array (Table × List (Fin 10 × Bool)) := #[(idT 16, [])]
  let mut i := 0
  for _ in [0:65536] do
    if i < queue.size then
      let (X, w) := queue[i]!
      i := i + 1
      for l in xLetters do
        let Y := compT 16 X (letTab l)
        let m := codeOf Y / 16
        if (arr[m]!).isNone then
          arr := arr.set! m (some (w ++ [l]))
          queue := queue.push (Y, w ++ [l])
  return arr

structure Ctx8 where
  ld : Array (Option (List (Fin 10 × Bool)))
  lt : Array Table
  tt : Array Table

@[expose] def mkCtx (_ : Unit := ()) : Ctx8 :=
  let ld := lBFS ()
  { ld := ld, lt := ld.map fun o => wTab (o.getD []),
    tt := (Array.range 16).map fun k => wTab (tw k) }

@[expose] def Ctx8.word (cx : Ctx8) (c : ℕ) : List (Fin 10 × Bool) :=
  tw (c % 16) ++ (cx.ld[c / 16]!).getD []

@[expose] def Ctx8.tab (cx : Ctx8) (c : ℕ) : Table := compT 16 cx.tt[c % 16]! cx.lt[c / 16]!

@[expose] def Ctx8.valid (cx : Ctx8) (c : ℕ) : Bool := (cx.ld[c / 16]!).isSome

@[expose] def Ctx8.codes (cx : Ctx8) : List ℕ := (List.range 1048576).filter cx.valid

@[expose] def relCheck : Bool := relsN8Ten.all fun r => wTab r == idT 16

@[expose] def ctxCheck (cx : Ctx8) : Bool :=
  cx.ld.size == 65536 && cx.codes.length == 322560 && cx.codes.all fun c => codeOf (cx.tab c) == c

@[expose] def Ctx8.isTt (cx : Ctx8) (X : Table) : Bool := X == cx.tt[codeOf X % 16]!

@[expose] def tCheck (cx : Ctx8) : Bool :=
  (List.range 16).all (fun k => (List.range 16).all fun l =>
    compT 16 cx.tt[k]! cx.tt[l]! == cx.tt[k ^^^ l]!) &&
  (List.range 16).all (fun k => (List.range 16).all fun l => !(cx.tt[k]! == cx.tt[l]!) || k == l) &&
  (List.range 16).all fun k => codeOf cx.tt[k]! % 16 == k

@[expose] def tNormCheck (cx : Ctx8) : Bool :=
  (List.finRange 10).all fun j => [true, false].all fun b => (List.range 16).all fun k =>
    (List.range 16).any fun l =>
      compT 16 (letTab (j, b)) cx.tt[k]! == compT 16 cx.tt[l]! (letTab (j, b))

@[expose] def b0T : Table := wTab (bWord 0)

@[expose] def b1T : Table := wTab (bWord 1)

@[expose] def b01T : Table := compT 16 b0T b1T

@[expose] def bList : List Table := [idT 16, b0T, b1T, b01T]

@[expose] def isBt (X : Table) : Bool := bList.contains X

@[expose] def commT (X Y : Table) : Bool := compT 16 X Y == compT 16 Y X

@[expose] def conjIn (X P : Table) (L : List Table) : Bool :=
  L.any fun K => compT 16 X P == compT 16 K X

@[expose] def conjInR (X P : Table) (L : List Table) : Bool :=
  L.any fun K => compT 16 P X == compT 16 X K

@[expose] def normK (L : List Table) (P Q X : Table) : Bool :=
  conjIn X P L && conjIn X Q L && conjInR X P L && conjInR X Q L

@[expose] def normB (X : Table) : Bool := normK bList b0T b1T X

@[expose] def bCheck (cx : Ctx8) : Bool :=
  compT 16 b0T b0T == idT 16 && compT 16 b1T b1T == idT 16 && commT b0T b1T &&
    !(b0T == idT 16) && !(b1T == idT 16) && !(b0T == b1T) && !(b01T == idT 16) &&
    !(b01T == b0T) && !(b01T == b1T) && !(cx.isTt b0T)

@[expose] def faMap (cx : Ctx8) (vc : List ℕ) : Array ℕ :=
  vc.foldl (fun arr c => let N := cx.tab c
    arr.set! (codeOf (compT 16 (compT 16 N b0T) (invT 16 N))) c) (Array.replicate 1048576 0)

@[expose] def Ctx8.commCount (cx : Ctx8) (X : Table) : ℕ :=
  (List.range 16).countP fun k => commT X cx.tt[k]!

@[expose] def faCheck (cx : Ctx8) : Bool :=
  let vc := cx.codes
  let fm := faMap cx vc
  vc.all fun c =>
    let X := cx.tab c
    !(compT 16 X X == idT 16) || cx.isTt X || decide (4 < cx.commCount X) ||
      (let n := fm[codeOf X]!
       decide (n < 1048576) && compT 16 (cx.tab n) b0T == compT 16 X (cx.tab n))

@[expose] def kList (X : Table) : List Table := [idT 16, b0T, X, compT 16 b0T X]

@[expose] def Ctx8.kleinPre (cx : Ctx8) (X : Table) : Bool :=
  compT 16 X X == idT 16 && commT X b0T && !(cx.isTt X) && !(cx.isTt (compT 16 b0T X)) &&
    !(X == b0T)

@[expose] def Ctx8.kleinCheap (cx : Ctx8) (X : Table) : Bool :=
  (List.range 16).countP (fun k => normK (kList X) b0T X cx.tt[k]!) == 4 &&
  (List.range 16).all (fun k => !(normK (kList X) b0T X cx.tt[k]!) ||
    (commT cx.tt[k]! b0T && commT cx.tt[k]! X)) &&
  (List.range 16).all fun k =>
    !(commT cx.tt[k]! b0T || commT cx.tt[k]! X || commT cx.tt[k]! (compT 16 b0T X)) ||
      normK (kList X) b0T X cx.tt[k]!

@[expose] def refutes (X Y : Table) : Bool :=
  (commT Y b0T || commT Y X || commT Y (compT 16 b0T X)) && !(normK (kList X) b0T X Y)

@[expose] def fbCheck (cx : Ctx8) : Bool :=
  let vc := cx.codes
  vc.all fun c =>
    let X := cx.tab c
    !(cx.kleinPre X) || !(cx.kleinCheap X) || isBt X || vc.any fun y => refutes X (cx.tab y)

end CFSG.CGT.M24R
