module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2Tests
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J2

open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.J2Cover CFSG.ComponentClassification.J2Cover.Models
open CFSG.Monster.B.Fischer

@[expose] def commA (x y : Array Nat) : Bool := eqA 315 (compA 315 x y) (compA 315 y x)

@[expose] def inEnum (c : ArrCert) (x : Array Nat) : Bool := c.pts.toList.any (eqA 315 x)

@[expose] def treeOK (xs : Array (Array Nat)) (u : Array Nat) : Bool :=
  let l0 := commutatorA 315 xs[0]! xs[1]!
  let l1 := commutatorA 315 xs[2]! xs[3]!
  let l2 := commutatorA 315 xs[4]! xs[5]!
  let l3 := commutatorA 315 xs[6]! xs[7]!
  let m0 := commutatorA 315 l0 l1
  let m1 := commutatorA 315 l2 l3
  xs.size == 8 && allLt 8 (fun i => validA 315 xs[i]!) && validA 315 l0 && validA 315 l1 &&
    validA 315 l2 && validA 315 l3 && validA 315 m0 && validA 315 m1 &&
    eqA 315 (commutatorA 315 m0 m1) u

@[expose] def j2EndE0OK (e0 : Array (Array Nat)) : Bool :=
  let cE := enumBfs 315 e0 j2PS j2Fuel
  enumOK 315 e0 j2PS cE && allLt e0.size (fun i => j2InP e0[i]!) &&
    allLt cE.pts.size (fun i => eqA 315 cE.pts[i]! (idA 315) || fixCountArr cE.pts[i]! == 15)

@[expose] def j2EndConjOK (e0 : Array (Array Nat)) (a0 c0 : Array Nat) (xs : Array (Array Nat)) :
    Bool :=
  let cE := enumBfs 315 e0 j2PS j2Fuel
  let e := e0[0]!
  (validA 315 a0 && j2InP a0 &&
    allLt e0.size (fun i => allLt e0.size fun j => commA e0[i]! (conjInvA 315 a0 e0[j]!)) &&
    !inEnum cE (conjInvA 315 a0 e)) &&
  (allLt xs.size (fun i => j2InP xs[i]! && allLt e0.size fun j => commA xs[i]! e0[j]!) &&
    treeOK xs (compA 315 e (conjInvA 315 a0 e))) &&
  (validA 315 c0 && j2InP c0 && eqA 315 (conjA 315 c0 e) autStrong[0]!)

@[expose] def j2EndDerOK (gN : Array (Array Nat)) : Bool :=
  let cN := enumBfs 315 gN j2PS j2Fuel
  let s := cent2BStrong
  enumOK 315 gN j2PS cN && validA 315 s[0]! && validA 315 s[1]! &&
    allLt 2 (fun i => allLt gN.size fun j =>
      inEnum cN (conjA 315 s[i]! gN[j]!) && inEnum cN (conjInvA 315 s[i]! gN[j]!)) &&
    inEnum cN (commutatorA 315 s[0]! s[1]!) &&
    allLt cN.pts.size (fun i => !eqA 315 (compA 315 cN.pts[i]! cN.pts[i]!) (idA 315) ||
      eqA 315 cN.pts[i]! (idA 315) || fixCountArr cN.pts[i]! != 15)

@[expose] def j2EndCheck (e0 : Array (Array Nat)) (a0 c0 : Array Nat)
    (xs gN : Array (Array Nat)) : Bool :=
  j2EndE0OK e0 && j2EndConjOK e0 a0 c0 xs && j2EndDerOK gN

end CFSG.ComponentClassification.RankTwoSporadic.J2
