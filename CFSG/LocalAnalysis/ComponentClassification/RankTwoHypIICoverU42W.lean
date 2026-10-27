module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverU42Check
public import CFSG.Certificates.Kernel.Census.ToMain

public section

namespace CFSG.ComponentClassification.RankTwoHypIICover.U42

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.KC.Census

@[expose] def u42FP : Nat :=
  0x1e7dd86281b71a668a67aecaa59a48d45535d85914903cd38c28b2472061050c1080

@[expose] noncomputable def u42CheckW (sG roots : Array ℕ) (nodes : Array NodeP) (cS : ArrCertP)
    (wcs : Array (Array ArrCertP)) : Bool :=
  rawChainOK 45 (u42S.extract 0 2) u42S u42Base
      (CFSG.EvenSmallLie.OmegaEight.wordsOf 2 u42Words) 4 &&
    censusOKW 45 u42PS u42InX u42InX false true false (sG.map (unpackP 45 6)) roots
      (nodes.map (NodeP.toMain 45 6)) (cS.toMain 45 6)
      (wcs.map fun cs => cs.map (ArrCertP.toMain 45 6)) &&
    (allLt (sG.map (unpackP 45 6)).size fun k =>
      u42InX (sG.map (unpackP 45 6))[k]! ||
        u42InX (compA 45 (unpackP 45 6 u42FP) (sG.map (unpackP 45 6))[k]!)) &&
    (cS.toMain 45 6).pts.size == 128

end CFSG.ComponentClassification.RankTwoHypIICover.U42
