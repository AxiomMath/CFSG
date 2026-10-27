module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12Tests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12Data
public import CFSG.Certificates.Kernel.Census.ToMainExc
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicExcW

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M12

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.RankThree.PartOne CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KC.Census

@[expose] def m12DW : List (List ℤ) := m12W.toList.drop 2

@[expose] noncomputable def m12CheckW (S : Array (Array ℕ)) (Wd : Array (List ℤ))
    (e0 : Array (Array ℕ)) (sG roots : Array ℕ) (nodes : Array NodeP) (cS : ArrCertP)
    (wcs : Array (Array ArrCertP)) (excs : List ExcRefP) : Bool :=
  decide (2 ≤ S.size) && caseChainOK2P 24 S m12BaseArr Wd m12A1Arr m12B1Arr &&
    censusExcOKW 24 m12PS (m12InP S) (m12InP S) (m12InR S) false false false
      (sG.map (unpackP 24 5)) roots (nodes.map (NodeP.toMain 24 5)) (cS.toMain 24 5)
      (wcs.map fun cs => cs.map (ArrCertP.toMain 24 5)) e0 (excs.map (ExcRefP.toMain 24 5)) &&
    (allLt (sG.map (unpackP 24 5)).size fun k =>
      m12InP S (sG.map (unpackP 24 5))[k]! ||
        m12InP S (compA 24 m12SigArr (sG.map (unpackP 24 5))[k]!)) &&
    (cS.toMain 24 5).pts.size == 128

end CFSG.ComponentClassification.RankTwoSporadic.M12
