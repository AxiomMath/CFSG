module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaCheck

public section

namespace CFSG.EvenSporadicStandard.Fin76b.Beta

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.HypOne

@[expose] def treeImgN (k : ℕ) (pg : Array Table) (par lab : Array ℕ) (m : ℕ) : Array Table :=
  Id.run do
    let mut r : Array Table := #[idT k]
    for j in [1:m] do
      r := r.push (compT k r[par[j]!]! pg[lab[j]!]!)
    return r

@[expose] def piA5J2 : Array Table := #[#[4, 1, 3, 2, 0], #[0, 3, 2, 4, 1]]

@[expose] def piA5J3 : Array Table := #[#[3, 1, 4, 0, 2], #[2, 0, 1, 3, 4]]

@[expose] def a5HomCheck (n : ℕ) (aT bT tT : Table) (pg : Array Table) : Bool :=
  let gens : Array Table := #[aT, bT]
  let E := mulClosureH n gens 100
  let elts := E.1
  let img := treeImgN 5 pg E.2.1 E.2.2 elts.size
  let idx := hashIndex n elts
  gens.all (fun x => permOK n x && invOK n x (invT n x)) && permOK n tT &&
    (pg.size == 2) && pg.all (fun x => permOK 5 x) && gens.all (fun x => commTT n tT x) &&
    mulTreeOK n gens elts E.2.1 E.2.2 && hkeysDistinct n elts.toList &&
    closedOKH n (gens ++ gens.map (invT n)) elts && elts.size == 60 &&
    (img.size == elts.size) && img.all (fun x => permOK 5 x) && tblEq 5 img[0]! (idT 5) &&
    (List.range elts.size).all (fun k => (List.range 2).all fun l =>
      let j := idxTH n elts idx (compT n elts[k]! gens[l]!)
      decide (j < elts.size) && tblEq 5 img[j]! (compT 5 img[k]! pg[l]!)) &&
    (List.range elts.size).all (fun k =>
      tblEq 5 img[k]! (idT 5) == tblEq n elts[k]! (idT n))

@[expose] def j2A5OK : Bool :=
  a5HomCheck 315 (j2BetaTbl 5) (j2BetaTbl 6) (j2BetaTbl 0) piA5J2

@[expose] def j3A5OK : Bool :=
  a5HomCheck 6156 (j3BetaTbl 5) (j3BetaTbl 6) (j3BetaTbl 0) piA5J3

@[expose] def j2A5MemOK : Bool :=
  j2Sift (j2BetaTbl 5) && j2Sift (j2BetaTbl 6) &&
    tblEq 315 (j2BetaTbl 6) (j2BetaTbl 7) && tblEq 315 (j2BetaTbl 0) (j2BetaTbl 8)

@[expose] def j3A5MemOK : Bool :=
  j3Sift (j3BetaTbl 5) && j3Sift (j3BetaTbl 6) &&
    tblEq 6156 (j3BetaTbl 6) (j3BetaTbl 7) && tblEq 6156 (j3BetaTbl 0) (j3BetaTbl 8)

end CFSG.EvenSporadicStandard.Fin76b.Beta
