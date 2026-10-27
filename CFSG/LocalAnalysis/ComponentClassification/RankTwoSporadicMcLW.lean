module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicMcLTests
public import CFSG.Certificates.Kernel.Census.ToMain

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.McL

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KC.Census

@[expose] noncomputable def mclCheckW (sG roots : Array ℕ) (nodes : Array NodeP) (cS : ArrCertP)
    (wcs : Array (Array ArrCertP)) : Bool :=
  censusOKW 275 mclPS mclInP mclInP false false false (sG.map (unpackP 275 9)) roots
      (nodes.map (NodeP.toMain 275 9)) (cS.toMain 275 9)
      (wcs.map fun cs => cs.map (ArrCertP.toMain 275 9)) &&
    (allLt (sG.map (unpackP 275 9)).size fun k =>
      mclInP (sG.map (unpackP 275 9))[k]! ||
        mclInP (compA 275 mclUArr (sG.map (unpackP 275 9))[k]!)) &&
    (cS.toMain 275 9).pts.size == 256

end CFSG.ComponentClassification.RankTwoSporadic.McL
