module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuEndData

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Ru

open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Fischer

@[expose] def ruEndB0 : Array ℕ := ruHexRow ruEndText.toUTF8 4060 0

@[expose] def ruEndLeaves : Array (Array ℕ) :=
  Array.ofFn (n := 8) fun i => ruHexRow ruEndText.toUTF8 4060 (i.val + 1)

@[expose] def ruEndN0 : Array (Array ℕ) :=
  Array.ofFn (n := 2) fun i => ruHexRow ruEndText.toUTF8 4060 (i.val + 9)

@[expose] def fpfA (t : Array ℕ) : Bool := allLt 4060 fun i => t[i]! != i

@[expose] def ruCommA (x y : Array ℕ) : Bool := eqA 4060 (compA 4060 x y) (compA 4060 y x)

@[expose] def ruInEnum (c : ArrCert) (x : Array ℕ) : Bool := c.pts.toList.any (eqA 4060 x)

@[expose] def ruTreeOK (xs : Array (Array ℕ)) (u : Array ℕ) : Bool :=
  let l0 := commutatorA 4060 xs[0]! xs[1]!
  let l1 := commutatorA 4060 xs[2]! xs[3]!
  let l2 := commutatorA 4060 xs[4]! xs[5]!
  let l3 := commutatorA 4060 xs[6]! xs[7]!
  let m0 := commutatorA 4060 l0 l1
  let m1 := commutatorA 4060 l2 l3
  xs.size == 8 && allLt 8 (fun i => validA 4060 xs[i]!) && validA 4060 l0 && validA 4060 l1 &&
    validA 4060 l2 && validA 4060 l3 && validA 4060 m0 && validA 4060 m1 &&
    eqA 4060 (commutatorA 4060 m0 m1) u

@[expose] def ruEndE0OK (e0 : Array (Array ℕ)) : Bool :=
  let cE := enumBfs 4060 e0 ruPS ruFuel
  enumOK 4060 e0 ruPS cE && allLt e0.size (fun i => ruInP e0[i]!) &&
    allLt cE.pts.size (fun i => eqA 4060 cE.pts[i]! (idA 4060) || fpfA cE.pts[i]!)

@[expose] def ruEndConjOK (e0 : Array (Array ℕ)) (b0 : Array ℕ) (xs : Array (Array ℕ)) :
    Bool :=
  let cE := enumBfs 4060 e0 ruPS ruFuel
  let e := e0[0]!
  (validA 4060 b0 && ruInP b0 &&
    allLt e0.size (fun i => allLt e0.size fun j => ruCommA e0[i]! (conjInvA 4060 b0 e0[j]!)) &&
    !ruInEnum cE (conjInvA 4060 b0 e)) &&
  (allLt xs.size (fun i => ruInP xs[i]! && allLt e0.size fun j => ruCommA xs[i]! e0[j]!) &&
    ruTreeOK xs (compA 4060 e (conjInvA 4060 b0 e)))

@[expose] def ruEndDerOK (lgs gN : Array (Array ℕ)) : Bool :=
  let cN := enumBfs 4060 gN ruPS ruFuel
  enumOK 4060 gN ruPS cN && allLt 3 (fun i => validA 4060 lgs[i]!) &&
    allLt 3 (fun i => allLt gN.size fun j =>
      ruInEnum cN (conjA 4060 lgs[i]! gN[j]!) && ruInEnum cN (conjInvA 4060 lgs[i]! gN[j]!)) &&
    allLt 3 (fun i => allLt 3 fun j => ruInEnum cN (commutatorA 4060 lgs[i]! lgs[j]!)) &&
    allLt cN.pts.size (fun i => !eqA 4060 (compA 4060 cN.pts[i]! cN.pts[i]!) (idA 4060) ||
      eqA 4060 cN.pts[i]! (idA 4060) || !fpfA cN.pts[i]!)

@[expose] def ruEndCheck (e0 : Array (Array ℕ)) (b0 : Array ℕ) (xs lgs gN : Array (Array ℕ)) :
    Bool :=
  ruEndE0OK e0 && ruEndConjOK e0 b0 xs && ruEndDerOK lgs gN

end CFSG.ComponentClassification.RankTwoSporadic.Ru
