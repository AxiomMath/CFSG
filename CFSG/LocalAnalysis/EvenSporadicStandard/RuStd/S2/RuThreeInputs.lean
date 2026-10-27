module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeData
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeProd
public import CFSG.RankThree.PartOne.KS.PKitLines
public import CFSG.RankThree.Native.ChainCentralizer

public noncomputable section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne

@[expose] def ruThreeKeys : List ℕ := ruThreeBase.map Fin.val

@[expose] def ruThreeBaseArr : Array ℕ := (ruThreeBase.map Fin.val).toArray

@[expose] def ruThreeLevels : Array Level := rawLevels 4060 ruThreeArrs ruThreeBaseArr

@[expose] def ruThreeQCert : ArrCert := enumBfs 4060 ruThreeQGens ruThreeKeys 40

@[expose] def ruThreeC0Cert : ArrCert := enumBfs 4060 ruThreeC0Gens ruThreeKeys 2180

@[expose] def ruThreeGraphCert : ArrCert :=
  prodBfs 4060 11 ruThreeC0Gens ruThreeM ruThreeKeys 2180

@[expose] def ruThreeInvOK : Bool :=
  !(eqA 4060 ruThreeC0Gens[1]! (idA 4060)) &&
    eqA 4060 (compA 4060 ruThreeC0Gens[1]! ruThreeC0Gens[1]!) (idA 4060) &&
    (List.range 4060).any fun p => (ruThreeC0Gens[1]!)[p]! == p

@[expose] def ruThreeKernelOK : Bool :=
  allLt ruThreeGraphCert.pts.size fun i =>
    !(eqA 11 (blk2 4060 11 ruThreeGraphCert.pts[i]!) (idA 11)) ||
      eqA 4060 (blk1 4060 ruThreeGraphCert.pts[i]!) (idA 4060) ||
      eqA 4060 (blk1 4060 ruThreeGraphCert.pts[i]!) ruThreeLines[0]! ||
      eqA 4060 (blk1 4060 ruThreeGraphCert.pts[i]!) (compA 4060 ruThreeLines[0]! ruThreeLines[0]!)

@[expose] def ruThreeKeys11 : List ℕ := List.range 11

@[expose] def ruThreeM11Cert : ArrCert := enumBfs 11 ruThreeM11 ruThreeKeys11 8000

@[expose] def ruThreeTCert : ArrCert := enumBfs 11 ruThreeM ruThreeKeys11 800

@[expose] def invA (n : ℕ) (t : Array ℕ) : Bool :=
  !(eqA n t (idA n)) && eqA n (compA n t t) (idA n)

@[expose] def oddNormalOK (n : ℕ) (c : ArrCert) : Bool :=
  allLt c.pts.size fun k => eqA n c.pts[k]! (idA n) ||
    (List.range 16).any (fun e => invA n (powArr n c.pts[k]! e)) ||
    c.pts.toList.any fun g => invA n (compA n c.pts[k]! (conjA n g c.pts[k]!))

@[expose] def ruThreeStabOK : Bool :=
  allLt ruThreeM.size fun k => ruThreeM11Cert.pts.toList.any (eqA 11 ruThreeM[k]!) &&
    (ruThreeM[k]!)[0]! == 0

@[expose] def ruThreeStabCoverOK : Bool :=
  allLt ruThreeM11Cert.pts.size fun i => !((ruThreeM11Cert.pts[i]!)[0]! == 0) ||
    ruThreeTCert.pts.toList.any (eqA 11 ruThreeM11Cert.pts[i]!)

@[expose] def ruThreeCenterOK : Bool :=
  allLt ruThreeTCert.pts.size fun k =>
    !(allLt ruThreeM.size fun l => commA 11 ruThreeTCert.pts[k]! ruThreeM[l]!) ||
      eqA 11 ruThreeTCert.pts[k]! (idA 11)

end CFSG.EvenSporadicStandard.RuStd.S2
