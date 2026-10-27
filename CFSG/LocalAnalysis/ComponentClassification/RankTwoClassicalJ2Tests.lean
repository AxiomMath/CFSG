module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalJ2Data
public import Certificates.Data.Kernel.J2StdOrbData
public import CFSG.RankThree.PartTwo.KFacts.KS14MultJ2Inputs
public meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalJ2Data
public meta import Certificates.Data.Kernel.J2StdOrbData
public meta import CFSG.RankThree.PartTwo.KFacts.KS14MultJ2Inputs

public section

namespace CFSG.ComponentClassification.RankTwoClassical.J2Std

open CFSG.ComponentClassification.J2Cover CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
  CFSG.RankThree.Native CFSG.Monster.B.Mathieu
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (keyPts okA inCert isTwoA)
open CFSG.RankThree.PartTwo.KFacts.KS14 (cE25)

@[expose] def j2StdZ (j : ℕ) : Array ℕ := if j = 0 then j2StdZ1 else j2StdZ2

@[expose] def j2StdH0 : Array ℕ := commutatorA 315 j2StdA1 j2StdB1

@[expose] def j2StdH1 : Array ℕ := commutatorA 315 j2StdA2 j2StdB2

@[expose] def j2StdH : Array (Array ℕ) := #[j2StdH0, j2StdH1]

@[expose] def cStdC1 : CFSG.Monster.B.Fischer.ArrCert := enumBfs 315 j2StdC1 keyPts 400

@[expose] def cStdC2 : CFSG.Monster.B.Fischer.ArrCert := enumBfs 315 j2StdC2 keyPts 100

@[expose] def cStdH : CFSG.Monster.B.Fischer.ArrCert := enumBfs 315 j2StdH keyPts 100

@[expose] def cStdCH : CFSG.Monster.B.Fischer.ArrCert := enumBfs 315 j2StdCH keyPts 20

@[expose] def j2StdElts : Bool :=
  okA j2StdZ1 && okA j2StdZ2 && eqA 315 (powArr 315 j2StdZ1 5) (idA 315) &&
    !(eqA 315 j2StdZ1 (idA 315)) && eqA 315 (powArr 315 j2StdZ2 5) (idA 315) &&
    !(eqA 315 j2StdZ2 (idA 315)) &&
    (allLt j2StdC1.size fun k => okA j2StdC1[k]! && commA j2StdC1[k]! j2StdZ1) &&
    (allLt j2StdC2.size fun k => okA j2StdC2[k]! && commA j2StdC2[k]! j2StdZ2) &&
    okA j2StdA1 && okA j2StdB1 && okA j2StdA2 && okA j2StdB2 &&
    commA j2StdA1 j2StdZ1 && commA j2StdB1 j2StdZ1 && commA j2StdA2 j2StdZ1 &&
    commA j2StdB2 j2StdZ1 && (allLt j2StdCH.size fun k => okA j2StdCH[k]!) &&
    (allLt j2StdH.size fun k => okA j2StdH[k]!) &&
    enumOK 315 j2StdC1 keyPts cStdC1 && cStdC1.pts.size == 300 &&
    enumOK 315 j2StdC2 keyPts cStdC2 && cStdC2.pts.size == 50 &&
    enumOK 315 j2StdH keyPts cStdH && cStdH.pts.size == 60 &&
    enumOK 315 j2StdCH keyPts cStdCH && cStdCH.pts.size == 10

@[expose] def conjProdW (c : CFSG.Monster.B.Fischer.ArrCert) (k : ℕ) (w : List ℕ) : Array ℕ :=
  w.foldl (fun r j => compA 315 r (conjA 315 c.pts[j]! c.pts[k]!)) (idA 315)

@[expose] def conjGenOK (c : CFSG.Monster.B.Fischer.ArrCert) (gs : Array (Array ℕ))
    (W : Array (Array (List ℕ))) : Bool :=
  allLt c.pts.size fun k => eqA 315 c.pts[k]! (idA 315) ||
    allLt gs.size fun i => ((W.getD k #[]).getD i []).all (· < c.pts.size) &&
      eqA 315 (conjProdW c k ((W.getD k #[]).getD i [])) gs[i]!

@[expose] def j2StdHChk : Bool :=
  (allLt cStdC1.pts.size fun k => !(isTwoA cStdC1.pts[k]!) || inCert cStdH cStdC1.pts[k]!) &&
    conjGenOK cStdH j2StdH j2StdSW

@[expose] def j2StdP5 : Bool :=
  j2StdW.size == 24 && j2StdConj.size == 24 && j2StdJ.size == 24 && j2StdK.size == 24 &&
    (allLt 24 fun i => okA j2StdConj[i]! && okA j2StdW[i]! &&
      eqA 315 (conjA 315 j2StdConj[i]! j2StdW[i]!) (powArr 315 (j2StdZ j2StdJ[i]!) j2StdK[i]!) &&
      (j2StdK[i]! == 1 || j2StdK[i]! == 2)) &&
    (allLt cE25.pts.size fun k => eqA 315 cE25.pts[k]! (idA 315) ||
      j2StdW.any (eqA 315 cE25.pts[k]!))

@[expose] def conjW (w : ℕ) (x : Array ℕ) : Array ℕ :=
  conjA 315 (prod3 315 autLevels (w / 1920) (w / 12 % 160) (w % 12)) x

@[expose] def keyAt (ps : List ℕ) (t : Array ℕ) : ℕ := ps.foldr (fun p acc => t[p]! + 512 * acc) 0

@[expose] def natChain : List ℕ → Bool
  | a :: b :: L => decide (a < b) && natChain (b :: L)
  | _ => true

@[expose] def orbOK (W : Array ℕ) (k : ℕ) (ps : List ℕ) (f : ℕ → Array ℕ) : Bool :=
  W.size == k && W.all (· < 604800) && natChain (W.toList.map fun w => keyAt ps (f w))

@[expose] def keyPts2 : List ℕ := [0, 4, 3, 315, 319, 318]

@[expose] def j2StdOrb : Bool :=
  orbOK j2StdOW1 2016 keyPts (conjW · j2StdZ1) &&
    orbOK j2StdOW2 12096 keyPts (conjW · j2StdZ2) &&
    orbOK j2StdOWH 60480 keyPts2 (fun w => conjW w j2StdH0 ++ conjW w j2StdH1) &&
    (allLt j2StdCH.size fun k => commA j2StdCH[k]! j2StdH0 && commA j2StdCH[k]! j2StdH1)

@[expose] def j2StdCheck : Bool := j2StdElts && j2StdHChk && j2StdP5 && j2StdOrb

end CFSG.ComponentClassification.RankTwoClassical.J2Std
