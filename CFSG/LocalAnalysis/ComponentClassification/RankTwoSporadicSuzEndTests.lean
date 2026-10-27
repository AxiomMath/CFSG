module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzEndData
public import CFSG.Sporadic.SuzOddCore.InvTCheckInputs

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Suz

open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Fischer

@[expose] def suzEndB0 : Array ℕ := hexTable 3 1782 0 suzEndText

@[expose] def suzEndLeaves : Array (Array ℕ) :=
  Array.ofFn (n := 8) fun i => hexTable 3 1782 (1782 * (i.val + 1)) suzEndText

@[expose] def suzEndL : Array (Array ℕ) :=
  Array.ofFn (n := 2) fun i => hexTable 3 1782 (1782 * (i.val + 9)) suzEndText

@[expose] def suzEndSigma : Array ℕ := hexTable 3 1782 (1782 * 11) suzEndText

@[expose] def suzEndC0 : Array ℕ := hexTable 3 1782 (1782 * 12) suzEndText

@[expose] def suzCommA (x y : Array ℕ) : Bool := eqA 1782 (compA 1782 x y) (compA 1782 y x)

@[expose] def suzInEnum (c : ArrCert) (x : Array ℕ) : Bool := c.pts.toList.any (eqA 1782 x)

@[expose] def suzTreeOK (xs : Array (Array ℕ)) (u : Array ℕ) : Bool :=
  let l0 := commutatorA 1782 xs[0]! xs[1]!
  let l1 := commutatorA 1782 xs[2]! xs[3]!
  let l2 := commutatorA 1782 xs[4]! xs[5]!
  let l3 := commutatorA 1782 xs[6]! xs[7]!
  let m0 := commutatorA 1782 l0 l1
  let m1 := commutatorA 1782 l2 l3
  xs.size == 8 && allLt 8 (fun i => validA 1782 xs[i]!) && validA 1782 l0 && validA 1782 l1 &&
    validA 1782 l2 && validA 1782 l3 && validA 1782 m0 && validA 1782 m1 &&
    eqA 1782 (commutatorA 1782 m0 m1) u

@[expose] def suzEndE0OK (e0 : Array (Array ℕ)) : Bool :=
  let cE := enumBfs 1782 e0 suzPS suzFuel
  enumOK 1782 e0 suzPS cE && cE.pts.size == 4 && allLt e0.size (fun i => suzInM e0[i]!) &&
    allLt e0.size (fun i => allLt e0.size fun j => suzCommA e0[i]! e0[j]!) &&
    allLt cE.pts.size (fun i => eqA 1782 cE.pts[i]! (idA 1782) || fixedCount cE.pts[i]! == 42)

@[expose] def suzEndConjOK (e0 : Array (Array ℕ)) (b0 : Array ℕ) (xs : Array (Array ℕ)) :
    Bool :=
  let cE := enumBfs 1782 e0 suzPS suzFuel
  let e := e0[0]!
  (validA 1782 b0 && suzInM b0 &&
    allLt e0.size (fun i => allLt e0.size fun j => suzCommA e0[i]! (conjInvA 1782 b0 e0[j]!)) &&
    !suzInEnum cE (conjInvA 1782 b0 e)) &&
  (allLt xs.size (fun i => suzInM xs[i]! && allLt e0.size fun j => suzCommA xs[i]! e0[j]!) &&
    suzTreeOK xs (compA 1782 e (conjInvA 1782 b0 e)))

@[expose] def suzEndDerOK (e0 gL : Array (Array ℕ)) (σ c0 : Array ℕ) : Bool :=
  let cE := enumBfs 1782 e0 suzPS suzFuel
  let cL := enumBfs 1782 gL suzPS suzFuel
  (enumOK 1782 gL suzPS cL && cL.pts.size == 20160 &&
    allLt gL.size (fun i => suzInM gL[i]! && allLt e0.size fun j => suzCommA gL[i]! e0[j]!) &&
    allLt cE.pts.size (fun i => eqA 1782 cE.pts[i]! (idA 1782) || !suzInEnum cL cE.pts[i]!) &&
    allLt cL.pts.size (fun i => !eqA 1782 (compA 1782 cL.pts[i]! cL.pts[i]!) (idA 1782) ||
      eqA 1782 cL.pts[i]! (idA 1782) || fixedCount cL.pts[i]! != 42)) &&
  (validA 1782 σ && suzInM σ && suzCommA σ e0[0]! && !suzCommA σ e0[1]! &&
    validA 1782 c0 && suzInM c0 && eqA 1782 (conjA 1782 c0 e0[0]!) (tArr 0))

@[expose] def suzEndCheck (e0 : Array (Array ℕ)) (b0 : Array ℕ) (xs gL : Array (Array ℕ))
    (σ c0 : Array ℕ) : Bool :=
  suzEndE0OK e0 && suzEndConjOK e0 b0 xs && suzEndDerOK e0 gL σ c0

end CFSG.ComponentClassification.RankTwoSporadic.Suz
