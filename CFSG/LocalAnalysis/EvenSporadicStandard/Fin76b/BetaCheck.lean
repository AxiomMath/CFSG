module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SylowFour
public import CFSG.Sporadic.SmallOddCore.J2CentralizerDInputs
public import CFSG.Sporadic.SmallOddCore.J3CheckInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic

public section

namespace CFSG.EvenSporadicStandard.Fin76b.Beta

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.HypOne
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Monster.B.Co2.Native

@[expose] def j2BetaHex : String := include_str "J2Beta.txt"

@[expose] def j3BetaHex : String := include_str "J3Beta.txt"

@[expose] def j2BetaTbl (k : ℕ) : Table := hexT 3 315 (315 * k) j2BetaHex

@[expose] def j3BetaTbl (k : ℕ) : Table := hexT 4 6156 (6156 * k) j3BetaHex

@[expose] def piGens : Array Table := #[#[1, 0, 4, 3, 2, 5], #[1, 3, 0, 2, 5, 4]]

@[expose] def treeImg (pg : Array Table) (par lab : Array ℕ) (m : ℕ) : Array Table := Id.run do
  let mut r : Array Table := #[idT 6]
  for k in [1:m] do
    r := r.push (compT 6 r[par[k]!]! pg[lab[k]!]!)
  return r

@[expose] def idxTH (n : ℕ) (L : Array Table) (idx : Std.HashMap UInt64 ℕ) (x : Table) : ℕ :=
  match idx[hkey n x]? with
  | some i => if i < L.size && tblEq n x L[i]! then i else L.size
  | none => L.size

@[expose] def betaHomCheck (n : ℕ) (tT dT bT : Table) (pg : Array Table) : Bool :=
  let gens : Array Table := #[tT, dT]
  let E := mulClosureH n gens 1100
  let elts := E.1
  let img := treeImg pg E.2.1 E.2.2 elts.size
  let idx := hashIndex n elts
  gens.all (fun x => permOK n x && invOK n x (invT n x)) && permOK n bT &&
    (pg.size == 2) && pg.all (fun x => permOK 6 x) &&
    ordTest n 3 bT && gens.all (fun x => commTT n bT x) &&
    mulTreeOK n gens elts E.2.1 E.2.2 && hkeysDistinct n elts.toList &&
    closedOKH n (gens ++ gens.map (invT n)) elts && elts.size == 1080 &&
    (img.size == elts.size) && img.all (fun x => permOK 6 x) && tblEq 6 img[0]! (idT 6) &&
    (List.range elts.size).all (fun k => (List.range 2).all fun l =>
      let j := idxTH n elts idx (compT n elts[k]! gens[l]!)
      decide (j < elts.size) && tblEq 6 img[j]! (compT 6 img[k]! pg[l]!)) &&
    (List.range elts.size).all (fun k =>
      tblEq 6 img[k]! (idT 6) == (tblEq n elts[k]! (idT n) || tblEq n elts[k]! bT ||
        tblEq n elts[k]! (compT n bT bT)))

@[expose] def j2BetaOK : Bool :=
  betaHomCheck 315 (j2BetaTbl 8) (j2BetaTbl 9) (j2BetaTbl 7) piGens

@[expose] def j3BetaOK : Bool :=
  betaHomCheck 6156 (j3BetaTbl 8) (j3BetaTbl 9) (j3BetaTbl 7) piGens

@[expose] def j2MemOK : Bool :=
  j2Sift (j2BetaTbl 8) && j2Sift (j2BetaTbl 9) && j2Sift (j2BetaTbl 7) &&
    tblEq 315 (j2BetaTbl 8) (j2CentTbl 31)

@[expose] def j3MemOK : Bool :=
  j3Sift (j3BetaTbl 8) && j3Sift (j3BetaTbl 9) && j3Sift (j3BetaTbl 7) &&
    tblEq 6156 (j3BetaTbl 8) (j3CentTbl 9)

@[expose] def sqW (n : ℕ) (b : Array ℕ) (w : List (Array ℕ)) : Bool :=
  allLt n fun i => evR w (evR w i) == b[i]!

@[expose] def j2CountComm : ℕ :=
  countW (commW 315 [natArr (j2BetaTbl 7)]) PairJ2.blocks []

@[expose] def j2CountSq : ℕ :=
  countW (sqW 315 (natArr (j2CentTbl 17))) PairJ2.blocks []

@[expose] def j3CountComm : ℕ :=
  PairJ3.parCount (commW 6156 [natArr (j3BetaTbl 7)]) PairJ3.blocks

end CFSG.EvenSporadicStandard.Fin76b.Beta
