module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12Tests

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M12

open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

@[expose] def m12FpfA (t : Array ℕ) : Bool := allLt 24 fun i => t[i]! != i

@[expose] def m12CommA (x y : Array ℕ) : Bool := eqA 24 (compA 24 x y) (compA 24 y x)

@[expose] def m12InEnum (c : ArrCert) (x : Array ℕ) : Bool := c.pts.toList.any (eqA 24 x)

@[expose] def m12T0 (e0 : Array (Array ℕ)) : Array ℕ := compA 24 e0[0]! e0[1]!

@[expose] def m12TreeOK (xs : Array (Array ℕ)) (u : Array ℕ) : Bool :=
  let l0 := commutatorA 24 xs[0]! xs[1]!
  let l1 := commutatorA 24 xs[2]! xs[3]!
  let l2 := commutatorA 24 xs[4]! xs[5]!
  let l3 := commutatorA 24 xs[6]! xs[7]!
  let m0 := commutatorA 24 l0 l1
  let m1 := commutatorA 24 l2 l3
  xs.size == 8 && allLt 8 (fun i => validA 24 xs[i]!) && validA 24 l0 && validA 24 l1 &&
    validA 24 l2 && validA 24 l3 && validA 24 m0 && validA 24 m1 &&
    eqA 24 (commutatorA 24 m0 m1) u

@[expose] def m12EndE0OK (S e0 : Array (Array ℕ)) : Bool :=
  let cE := enumBfs 24 e0 m12PS m12Fuel
  e0.size == 2 && enumOK 24 e0 m12PS cE && cE.pts.size == 4 &&
    allLt e0.size (fun i => allLt e0.size fun j => m12CommA e0[i]! e0[j]!) &&
    allLt cE.pts.size (fun i => eqA 24 cE.pts[i]! (idA 24) || m12FpfA cE.pts[i]!) &&
    eqA 24 (compA 24 (m12T0 e0) (m12T0 e0)) (idA 24) && m12InP S (m12T0 e0)

@[expose] def m12EndConjOK (S e0 : Array (Array ℕ)) (a0 : Array ℕ) (xs : Array (Array ℕ)) :
    Bool :=
  let cE := enumBfs 24 e0 m12PS m12Fuel
  let t := m12T0 e0
  (validA 24 a0 && m12InP S a0 &&
    allLt e0.size (fun i => allLt e0.size fun j => m12CommA e0[i]! (conjInvA 24 a0 e0[j]!)) &&
    !m12InEnum cE (conjInvA 24 a0 t)) &&
  (allLt xs.size (fun i => m12InP S xs[i]! && allLt e0.size fun j => m12CommA xs[i]! e0[j]!) &&
    m12TreeOK xs (compA 24 t (conjInvA 24 a0 t)))

@[expose] def m12EndDerOK (S e0 gL : Array (Array ℕ)) (σ c0 z : Array ℕ) : Bool :=
  let cL := enumBfs 24 gL m12PS m12Fuel
  let t := m12T0 e0
  (enumOK 24 gL m12PS cL && cL.pts.size == 60 &&
    allLt gL.size (fun i => m12InP S gL[i]! && allLt e0.size fun j => m12CommA gL[i]! e0[j]!) &&
    !m12InEnum cL t &&
    allLt cL.pts.size (fun i => !eqA 24 (compA 24 cL.pts[i]! cL.pts[i]!) (idA 24) ||
      eqA 24 cL.pts[i]! (idA 24) || !m12FpfA cL.pts[i]!)) &&
  (validA 24 σ && m12InP S σ && m12CommA σ t && !m12CommA σ e0[0]! &&
    validA 24 c0 && m12InP S c0 && eqA 24 (conjA 24 c0 t) z)

@[expose] def m12EndCheck (S e0 : Array (Array ℕ)) (a0 : Array ℕ) (xs gL : Array (Array ℕ))
    (σ c0 z : Array ℕ) : Bool :=
  m12EndE0OK S e0 && m12EndConjOK S e0 a0 xs && m12EndDerOK S e0 gL σ c0 z

@[expose] def m12PowA (t : Array ℕ) : ℕ → Array ℕ
  | 0 => idA 24
  | e + 1 => compA 24 t (m12PowA t e)

@[expose] def m12OverCentOK (S e0 cw : Array (Array ℕ)) : Bool :=
  let cC := enumBfs 24 cw m12PS m12Fuel
  enumOK 24 cw m12PS cC && cC.pts.size == 240 &&
    allLt cw.size (fun i => m12InR S cw[i]! && allLt e0.size fun j => m12CommA cw[i]! e0[j]!) &&
    allLt cC.pts.size (fun i => !eqA 24 (m12PowA cC.pts[i]! 4) (idA 24) ||
      eqA 24 (compA 24 cC.pts[i]! cC.pts[i]!) (idA 24))

@[expose] def m12OverHOK (S e0 : Array (Array ℕ)) (h0 : Array ℕ) : Bool :=
  validA 24 h0 && m12InP S h0 && m12CommA h0 (m12T0 e0) &&
    eqA 24 (commutatorA 24 h0 e0[0]!) (m12T0 e0)

end CFSG.ComponentClassification.RankTwoSporadic.M12
