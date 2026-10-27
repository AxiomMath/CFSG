module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Index
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Multi
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeSylArr
public import CFSG.Sporadic.SmallOddCore.J2DataInputs

public section

namespace CFSG.QuasithinUnique.Bridge.J2Excl
open CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def j2A0A : Array ℕ := j2StrongArrs[0]!

@[expose] def j2A1A : Array ℕ := j2StrongArrs[1]!

@[expose] def j2A0P : PArr := (j2A0A, invCand 315 j2A0A)

@[expose] def j2A1P : PArr := (j2A1A, invCand 315 j2A1A)

@[expose] def j2TA (k : ℕ) : Array ℕ := natArr (j2CentTbl k)

@[expose] def j2TP (k : ℕ) : PArr := (j2TA k, j2TA k)

@[expose] def j2SP (k : ℕ) : PArr := (j2TA k, invCand 315 (j2TA k))

@[expose] def j2SylGens : List PArr :=
  [j2SP 1, j2SP 2, j2SP 3, j2SP 4, j2SP 5, j2SP 6, j2SP 7, j2SP 8]

@[expose] def j2Par : List ℕ := parseNats j2SylParStr

@[expose] def j2Lab : List ℕ := parseNats j2SylLabStr

@[expose] def j2Tab : List ℕ := parseNats j2SylTabStr

@[expose] def j2Al : Array (Array ℕ) := sylBuild 315 256 j2SylGens j2Par j2Lab

@[expose] def j2Mt : Array ℕ :=
  (List.range 256).foldl (fun acc i => (List.range 256).foldl (fun acc2 j =>
    acc2.push (if j = 0 then i else
      j2Tab.getD (acc2.getD (i * 256 + j2Par.getD j 0) 0 * 8 + j2Lab.getD j 0) 0)) acc) #[]

@[expose] def j2Mul (i j : ℕ) : ℕ := j2Mt.getD (i * 256 + j) 0

@[expose] def j2MulOK : Bool :=
  allLt 256 fun i => allLt 256 fun j => decide (j2Mul i j < 256) &&
    (if j = 0 then j2Mul i 0 == i else
      j2Mul i j == j2Tab.getD (j2Mul i (j2Par.getD j 0) * 8 + j2Lab.getD j 0) 0)

@[expose] def j2InvT : Array ℕ :=
  ((List.range 256).map fun s => (List.range 256).findIdx fun j => j2Mul s j == 0).toArray

@[expose] def j2Inv (s : ℕ) : ℕ := j2InvT.getD s 0

@[expose] def j2InvOK : Bool := allLt 256 fun s => decide (j2Inv s < 256) && j2Mul s (j2Inv s) == 0

@[expose] def j2Reps : List (ℕ × ℕ) := j2PairData.map fun e => (e.1, e.2.1)

@[expose] def j2RepsOK : Bool :=
  j2Reps.all fun ab => decide (ab.1 < 256) && decide (ab.2 < 256) && isInvF j2Mul ab.1 &&
    isInvF j2Mul ab.2

@[expose] def j2GoodTbl : Array Bool := goodTblF 256 j2Mul j2Inv j2Reps

@[expose] def j2Good (i j : ℕ) : Bool := j2GoodTbl.getD (i * 256 + j) false

@[expose] def j2TripleOK : Bool := tripleOKF 256 j2Mul j2Good

@[expose] def j2PairCertsOK : Bool :=
  j2PairData.all fun e => e.2.2.1.length == 2 &&
    multiConjCheck 315 [j2A0P, j2A1P] [(j2Al[e.1]!, j2Al[e.1]!), (j2Al[e.2.1]!, j2Al[e.2.1]!)]
      e.2.2.1 e.2.2.2 [j2A0A, j2A1A]

@[expose] def j2FX : PArr := pWord 315 [j2A0P, j2A1P] j2FrobXWord

@[expose] def j2FG : PArr := pWord 315 [j2A0P, j2A1P] j2FrobGWord

@[expose] def j2FY : PArr := pConj 315 j2FG j2FX

@[expose] def j2FrobOK : Bool :=
  eqA 315 (pMul 315 (pMul 315 j2FX j2FX) (pMul 315 (pMul 315 j2FX j2FX) j2FX)).1 (idA 315) &&
    !eqA 315 j2FX.1 (idA 315) &&
    eqA 315 (pMul 315 j2FX j2FY).1 (pMul 315 j2FY j2FX).1 &&
    eqA 315 (pConj 315 j2FG j2FY).1 (pInv (pMul 315 j2FX j2FY)).1

end CFSG.QuasithinUnique.Bridge.J2Excl
