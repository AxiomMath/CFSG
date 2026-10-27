module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalJ2Tests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSp44J2Data
public meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalJ2Tests
public meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSp44J2Data

public section

namespace CFSG.ComponentClassification.RankTwoClassical.J2Std

open CFSG.ComponentClassification.J2Cover CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
  CFSG.RankThree.Native CFSG.Monster.B.Mathieu
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (keyPts okA inCert)

@[expose] def j2A4RGens : Array (Array ℕ) := #[j2A4R1, j2A4R2]

@[expose] def cA4R : CFSG.Monster.B.Fischer.ArrCert := enumBfs 315 j2A4RGens keyPts 8

@[expose] def cA4CR : CFSG.Monster.B.Fischer.ArrCert := enumBfs 315 j2A4CR keyPts 300

@[expose] def cA4L : CFSG.Monster.B.Fischer.ArrCert := enumBfs 315 j2A4L keyPts 100

@[expose] def cA4C3 : CFSG.Monster.B.Fischer.ArrCert := enumBfs 315 j2A4C3 keyPts 50

@[expose] def j2A4Elts : Bool :=
  okA j2A4R1 && okA j2A4R2 && okA j2A4F && okA j2A4Z3 &&
    (allLt j2A4CR.size fun k => okA j2A4CR[k]! && commA j2A4CR[k]! j2A4R1 &&
      commA j2A4CR[k]! j2A4R2) &&
    (allLt j2A4L.size fun k => okA j2A4L[k]! && inCert cA4CR j2A4L[k]!) &&
    (allLt j2A4C3.size fun k => okA j2A4C3[k]! && commA j2A4C3[k]! j2A4Z3) &&
    enumOK 315 j2A4RGens keyPts cA4R && cA4R.pts.size == 4 &&
    enumOK 315 j2A4CR keyPts cA4CR && cA4CR.pts.size == 240 &&
    enumOK 315 j2A4L keyPts cA4L && cA4L.pts.size == 60 &&
    enumOK 315 j2A4C3 keyPts cA4C3 && cA4C3.pts.size == 36 &&
    inCert cStdH j2A4R1 && inCert cStdH j2A4R2 &&
    (allLt j2A4CR.size fun k => allLt j2A4L.size fun l =>
      inCert cA4L (conjA 315 j2A4CR[k]! j2A4L[l]!)) &&
    (allLt j2A4CR.size fun k => allLt j2A4CR.size fun l =>
      inCert cA4L (commutatorA 315 j2A4CR[k]! j2A4CR[l]!)) &&
    eqA 315 (powArr 315 j2A4F 3) (idA 315) && !(eqA 315 j2A4F (idA 315)) &&
    (allLt j2A4L.size fun k => commA j2A4F j2A4L[k]!) &&
    inCert cA4R (conjA 315 j2A4F j2A4R1) && inCert cA4R (conjA 315 j2A4F j2A4R2) &&
    !(commA j2A4F j2A4R1 && commA j2A4F j2A4R2) &&
    eqA 315 (powArr 315 j2A4Z3 3) (idA 315) && !(eqA 315 j2A4Z3 (idA 315)) &&
    inCert cA4L j2A4Z3 &&
    (allLt cA4C3.pts.size fun k => !(eqA 315 (powArr 315 cA4C3.pts[k]! 5) (idA 315)) ||
      eqA 315 cA4C3.pts[k]! (idA 315))

@[expose] def j2A4Orb : Bool :=
  orbOK j2A4OWR 2520 keyPts2 (fun w => conjW w j2A4R1 ++ conjW w j2A4R2) &&
    orbOK j2A4OW3 16800 keyPts (conjW · j2A4Z3)

@[expose] def j2A4Check : Bool := j2A4Elts && j2A4Orb

end CFSG.ComponentClassification.RankTwoClassical.J2Std
