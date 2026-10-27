module

public import Certificates.Data.CatFactsL4U4P1L43Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYLin

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpTC7

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.EvenSporadicStandard.HSStd.FiveY CFSG.Sporadic.SmallOddCore.Native
  CFSG.Certificates.Native CFSG.ComponentClassification.HarrisLit.P1
  CFSG.ComponentClassification.HarrisLit.P1.L43

open CFSG.Sporadic.Th.Native (Table)

@[expose] def rows43 : List Row := l43Runs.flatMap (·.rows)

@[expose] def gsP : Array (Array ℕ) := pgTbls.map natArr

@[expose] def keys43 : List ℕ :=
  CFSG.ComponentClassification.HarrisLit.P1.L43.chainBase.map Fin.val

@[expose] def cgArr (r : Row) : Array (Array ℕ) := (r.row.centGens.map natArr).toArray

@[expose] def isOrd3 (a : Array ℕ) : Bool :=
  !eqA 80 a (idA 80) && eqA 80 (compA 80 a (compA 80 a a)) (idA 80)

@[expose] def survCheck (r : Row) (ec : ArrCert) (x0 : Array ℕ) (cc : ArrCert) : Bool :=
  enumOKL 80 (cgArr r) keys43 ec && allLt gsP.size (fun k => validA 80 gsP[k]!) && isOrd3 x0 &&
    arrCertOKL (fun k a => conjA 80 gsP[k]! a) gsP.size (validA 80) (keyA 80 keys43) x0 cc &&
    cc.pts.size == 74880 && ec.pts.toList.all fun a => !isOrd3 a || cc.pts.toList.any (eqA 80 a)

@[expose] def survOK43 (r : Row) : Bool :=
  let ec := enumBfs 80 (cgArr r) keys43 800
  let x0 := (ec.pts.toList.filter isOrd3).headD (idA 80)
  survCheck r ec x0
    (arrBfs (fun k a => conjA 80 gsP[k]! a) gsP.size (keyA 80 keys43) x0 80000)

@[expose] def derComms (r : Row) (pairs : List (List ℤ × List ℤ)) : Array (Array ℕ) :=
  (pairs.map fun p => commutatorA 80 (wordA 80 (cgArr r) (rawInvs 80 (cgArr r)) p.1)
    (wordA 80 (cgArr r) (rawInvs 80 (cgArr r)) p.2)).toArray

@[expose] def derCheck (r : Row) (pairs : List (List ℤ × List ℤ)) (ec : ArrCert) : Bool :=
  allLt (cgArr r).size (fun k => validA 80 (cgArr r)[k]!) &&
    pairs.all (fun p => lettersOK (cgArr r).size p.1 && lettersOK (cgArr r).size p.2) &&
    enumOKL 80 (derComms r pairs) keys43 ec && ec.pts.size == 720

@[expose] def derOK43 (r : Row) (pairs : List (List ℤ × List ℤ)) : Bool :=
  derCheck r pairs (enumBfs 80 (derComms r pairs) keys43 800)

@[expose] def derPairs : List (Table × List (List ℤ × List ℤ)) := [
  (tm 11821474, [([-2, -1], [2, 2, 2]), ([2, 1, 1], [2, 2, 2]), ([-1, 2, 1], [-2]),
    ([-1, -2, -1], [1, -2])]),
  (tm 40942156, [([1, 2, -1], [1, -2, -2]), ([2, 2], [-1, -1])]),
  (tm 12703935, [([-2, -2, -1], [2, -1, -2]), ([2, 1, -2], [-2, 1, -2]), ([-2, 1], [2, 2, 2])])]

@[expose] def rowOK43 (r : Row) : Bool :=
  !decide (r.row.centOrder ∣ 2880) || decide (r.row.centOrder * 4 < 2880) ||
    (r.row.centOrder == 2880 &&
      match derPairs.find? (fun p => p.1 == r.row.rep) with
      | some p => derOK43 r p.2
      | none => false) ||
    (r.row.centOrder == 720 && survOK43 r)

@[expose] def h43OK : Bool :=
  rows43.length == 11 && rows43.all rowOK43

end CFSG.EvenSporadicStandard.HSStd.PumpTC7
