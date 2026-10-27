module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.M11Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeVCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvCheck

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose, noinline] def ordInS (idt x : Table) : Bool :=
  tblEq 1408 (powT 1408 8 x) idt || tblEq 1408 (powT 1408 6 x) idt ||
    tblEq 1408 (powT 1408 5 x) idt || tblEq 1408 (powT 1408 11 x) idt

@[expose, noinline] def ordAllOK (idt : Table) (L : Array Table) : Bool := L.all (ordInS idt)

@[expose, noinline] def probeT (ys : Array Table) (tj : Table) (p : List ℕ) : Table :=
  p.foldl (fun acc e => compT 1408 acc (compT 1408 ys[e]! tj)) (idT 1408)

@[expose, noinline] def m11JOK (idt n1 n1i : Table) (ys L0 : Array Table) (tj : Table) : Bool :=
  m11Probes.any (fun p => !ordInS idt (probeT ys tj p)) || memT 1408 L0 tj ||
    memT 1408 L0 (conjT 1408 n1 n1i tj)

@[expose, noinline] def m11ClassOK (idt n1 n1i : Table) (ys L0 Lc : Array Table) : Bool :=
  Lc.all (m11JOK idt n1 n1i ys L0)

@[expose] def m11Relators : List (List (ℕ × Bool)) :=
  [[(1, true), (0, false), (0, false), (0, false), (1, true), (0, false), (1, true), (1, true),
      (1, true)],
    [(1, true), (0, true), (1, false), (0, false), (1, false), (0, false), (1, true), (0, true),
      (1, false), (0, true)]]

@[expose, noinline] def relTab (ta tb tai tbi : Table) (w : List (ℕ × Bool)) : Table :=
  w.foldl (fun acc l => compT 1408 acc
    (if l.1 = 0 then (if l.2 then ta else tai) else if l.1 = 1 then (if l.2 then tb else tbi)
      else idT 1408)) (idT 1408)

@[expose] def m11GroupOK (L0 : Array Table) : Bool :=
  let idt := idT 1408
  let ty := tabW y0Word
  let tv := tabW vWord
  let tyi := invT 1408 ty
  let tvi := invT 1408 tv
  enumW invCap 7920 [y0Word, vWord] && primeOrderOK 11 ty && primeOrderOK 11 tv &&
    !commTT 1408 ty tv && invOK 1408 ty tyi && invOK 1408 tv tvi &&
    m11Relators.all (fun w => tblEq 1408 (relTab ty tv tyi tvi w) idt) && ordAllOK idt L0 &&
    wordOK i0Word && primeOrderOK 2 (tabW i0Word) && wordsInOK L0 [i0Word] &&
    enumW invCap 7920 [y0Word, i0Word]

@[expose, noinline] def powsT (ty : Table) : Array Table :=
  #[powT 1408 0 ty, powT 1408 1 ty, powT 1408 2 ty, powT 1408 3 ty, powT 1408 4 ty,
    powT 1408 5 ty]

@[expose] def m11ClassesOK (L0 : Array Table) : Bool :=
  let idt := idT 1408
  let ty := tabW y0Word
  let n1 := tabW n1Word
  let n1i := invT 1408 n1
  let ys : Array Table := powsT ty
  conjEqOK n1Word ty (powT 1408 7 ty) &&
    m11ClassOK idt n1 n1i ys L0 (classList invCap classz.rep) &&
    m11ClassOK idt n1 n1i ys L0 (classList invCap classaz.rep)

@[expose] def m11FiveOK (L0 : Array Table) : Bool :=
  let tr := tabW rho0Word
  wordOK fix5B.rep && primeOrderOK 5 tr && wordsInOK L0 [rho0Word, ck2Word, ck3Word, ck4Word] &&
    conjEqOK ck2Word tr (powT 1408 2 tr) && conjEqOK ck3Word tr (powT 1408 3 tr) &&
    conjEqOK ck4Word tr (powT 1408 4 tr) && conjEqOK cBWord tr (tabW fix5B.rep)

@[expose] def m11OK : Bool :=
  let L0 := subgroupList invCap [y0Word, vWord]
  m11GroupOK L0 && m11ClassesOK L0 && m11FiveOK L0

end CFSG.EvenSporadicStandard.HNRecog
