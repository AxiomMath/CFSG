module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThFiveCentInputs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne

open CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFiveNative
  CFSG.HardMathSupport.Dickson.I271

set_option compiler.extract_closed false

@[expose] def thPlaneEig (_ : Unit := ()) : List (Nat × Nat × Nat × Nat) :=
  [(25, 0, 1, 2), (84, 0, 1, 3), (82, 3, 1, 1)]

@[expose] def thPlaneWordA (_ : Unit := ()) : List Nat :=
  [84, 82, 25, 84, 84, 84, 82, 25, 82, 25, 84, 84, 84, 25, 25, 25, 82, 25, 84, 84, 84, 82, 25, 25,
    25, 84, 84, 84, 82, 84, 25, 82, 25, 25, 25, 84, 84, 84, 82, 84, 25, 82, 84, 25, 25, 25, 82, 25,
    84, 25, 25, 25, 82, 25, 25, 25, 82, 84, 25, 25, 25, 82, 84, 84, 84]

@[expose] def thPlaneWordB (_ : Unit := ()) : List Nat :=
  [25, 25, 25, 82, 84, 84, 84, 25, 82, 84, 25, 82, 84, 84, 25, 84, 84, 84, 25, 82, 84, 84, 84, 25,
    82, 25, 25, 25, 25, 84, 84, 82, 25, 84, 84, 82, 25, 84, 84, 82, 25, 84, 84, 82, 25, 84, 84, 82,
    25, 84, 84, 82, 25, 84, 84, 82, 25, 82, 25, 25, 25, 84, 82, 25, 25, 25, 84, 25, 25, 25, 84, 84,
    82, 25, 25, 25, 84, 84, 84, 82, 25, 25, 25, 84, 82, 25]

@[expose] def thPlaneConj (_ : Unit := ()) : Array (List Nat × Nat × Nat) :=
  #[([], 0, 0), ([], 1, 0), ([], 3, 0), ([], 2, 0), ([], 4, 0), ([19, 99], 4, 1), ([19], 2, 0),
    ([114, 99], 3, 0), ([99], 3, 1), ([114], 3, 3), ([19, 99], 2, 1), ([99], 4, 4), ([19], 1, 4),
    ([114], 4, 2), ([114, 99], 4, 2), ([19, 99], 3, 1), ([114, 99], 1, 4), ([114], 1, 1),
    ([19], 4, 3), ([99], 1, 2), ([19, 99], 1, 1), ([114], 2, 0), ([99], 2, 0), ([114, 99], 2, 1),
    ([19], 3, 2)]

@[expose, noinline] def thPlaneEigOK (regs : Array (Array V4)) (I X Y C : Array V4)
    (e : Nat × Nat × Nat × Nat) : Bool :=
  let W := cubeProd X Y C 0 e.2.1 e.2.2.1
  decide (e.1 < regs.size) && rowsDiffer W I && eqRows (powRowsN W 5) I &&
    eqRows (mulRows regs[e.1]! W) (mulRows (powRowsN W e.2.2.2) regs[e.1]!)

@[expose, noinline] def thPlaneConjOK (regs : Array (Array V4)) (X Y C : Array V4)
    (d : List Nat × Nat × Nat) (i j : Nat) : Bool :=
  d.1.all (fun r => decide (r < regs.size)) &&
    (let M := wordRowsL regs d.1
     eqRows (mulRows M C) (mulRows C M) &&
       eqRows (mulRows M Y)
         (mulRows (mulRows (powRowsN (mulRows (powRowsN X i) (powRowsN Y j)) d.2.1)
           (powRowsN C d.2.2)) M))

@[expose, noinline] def thPlaneCore (regs : Array (Array V4)) : Bool :=
  let I := idRows ()
  let X := regs[94]!
  let Y := regs[105]!
  let C := mulRows (mulRows (mulRows X Y) (powRowsN X 4)) (powRowsN Y 4)
  let E := thPlaneEig ()
  let G := E.map Prod.fst
  let wA := thPlaneWordA ()
  let wB := thPlaneWordB ()
  let D := thPlaneConj ()
  E.all (thPlaneEigOK regs I X Y C) && wA.all (fun r => G.contains r) &&
    wB.all (fun r => G.contains r) && wA.all (fun r => decide (r < regs.size)) &&
    wB.all (fun r => decide (r < regs.size)) && eqRows (wordRowsL regs wA) (rowsOf seedA) &&
    eqRows (wordRowsL regs wB) (rowsOf seedB) &&
    (List.range 5).all fun i => (List.range 5).all fun j =>
      i + j == 0 || thPlaneConjOK regs X Y C D[5 * i + j]! i j

@[expose] def thPlaneOK (_ : Unit := ()) : Bool :=
  thPlaneCore (slpRows (rowsOf seedA) (rowsOf seedB) 118 prog5)

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne
