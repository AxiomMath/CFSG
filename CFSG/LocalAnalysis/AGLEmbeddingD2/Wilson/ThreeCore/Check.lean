module

public import CFSG.Sporadic.SmallOddCore.CentData

public section

namespace CFSG.AGLEmbeddingD2.Wilson.ThreeCore

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.SmallOddCore

@[expose] def threeRowOK (n cap : Nat) (sift : Table → Bool) (t : Table) (cg cgInv : Array Table)
    (s : OddRow) : Bool :=
  permOK n s.rep && sift s.rep && commTT n s.rep t && ordTest n s.prime s.rep &&
    match s.wit with
    | .conj h ord => permOK n h && sift h && commTT n h t && invOK n h (invT n h) &&
        ord % 3 == 0 && 0 < ord && ordTest n ord (compT n s.rep (conjT n h (invT n h) s.rep))
    | .normal gs _ =>
        let q := conjClosureH n cg cgInv s.rep cap
        let e := mulClosureH n gs.toArray cap
        conjTreeOK n cg cgInv s.rep q.1 q.2.1 q.2.2 &&
          gs.all (fun g => permOK n g && memT n q.1 g) &&
          mulTreeOK n gs.toArray e.1 e.2.1 e.2.2 && e.1.any (ordTest n 3)

@[expose] def threeClassOK (n NP cap : Nat) (pg pgInv : Array Table) (sift : Table → Bool)
    (r : ClassRow) (o : Closure) : Bool :=
  let t := r.rep
  let cg := r.centGens.toArray
  let cgInv := cg.map (invT n)
  let C := mulClosureH n cg cap
  let queues := r.odd.map fun s => (s, conjClosureH n cg cgInv s.rep cap)
  permOK n t && ordTest n 3 t && sift t &&
    conjTreeOK n pg pgInv t o.1 o.2.1 o.2.2 && hkeysDistinct n o.1.toList &&
    o.1.size == r.classSize &&
    cg.all (fun c => permOK n c && sift c && commTT n c t && invOK n c (invT n c)) &&
    mulTreeOK n cg C.1 C.2.1 C.2.2 && hkeysDistinct n C.1.toList && C.1.size == r.centOrder &&
    r.classSize * r.centOrder == NP &&
    r.odd.all (threeRowOK n cap sift t cg cgInv) &&
    queues.all (fun q => conjTreeOK n cg cgInv q.1.rep q.2.1 q.2.2.1 q.2.2.2) &&
    C.1.all (fun y => !selOK n r.oddPrimes y || queues.any (fun q => memT n q.2.1 y))

@[expose] def threeSylowOK (n cap : Nat) (pg pgInv : Array Table) (sift : Table → Bool)
    (sylowGens : List Table) (sylowOrder : Nat) : Bool :=
  let sg := sylowGens.toArray
  let syl := mulClosureH n sg cap
  pg.size == pgInv.size && allIn 0 pg.size (fun l => invOK n pg[l]! pgInv[l]!) &&
    sg.all (fun x => permOK n x && invOK n x (invT n x) && sift x) &&
    mulTreeOK n sg syl.1 syl.2.1 syl.2.2 && closedOK n (sg ++ sg.map (invT n)) syl.1 &&
    hkeysDistinct n syl.1.toList && syl.1.size == sylowOrder

@[expose] def threeCoverOK (n cap : Nat) (sylowGens : List Table)
    (rowsO : List (ClassRow × Closure)) : Bool :=
  let syl := mulClosureH n sylowGens.toArray cap
  syl.1.all (fun s => !ordTest n 3 s || rowsO.any (fun p => memT n p.2.1 s))

@[expose] def threeDataOK (n NP cap : Nat) (pg pgInv : Array Table) (sift : Table → Bool)
    (sylowGens : List Table) (sylowOrder : Nat) (rows : List ClassRow) : Bool :=
  let rowsO := rows.map fun r => (r, conjClosureH n pg pgInv r.rep cap)
  threeSylowOK n cap pg pgInv sift sylowGens sylowOrder &&
    rowsO.all (fun p => threeClassOK n NP cap pg pgInv sift p.1 p.2) &&
    threeCoverOK n cap sylowGens rowsO

end CFSG.AGLEmbeddingD2.Wilson.ThreeCore
