module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2Tests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicExcW
public import CFSG.Certificates.Kernel.Census.ToMainExc

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J2

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.J2Cover
open CFSG.KC.Census

@[expose] noncomputable def j2CheckWII (sG roots : Array ℕ) (nodes : Array NodeP)
    (cS : ArrCertP) (wcs : Array (Array ArrCertP)) : Bool :=
  censusOKW 315 j2PS j2InP j2InP false true false (sG.map (unpackP 315 9)) roots
      (nodes.map (NodeP.toMain 315 9)) (cS.toMain 315 9)
      (wcs.map fun cs => cs.map (ArrCertP.toMain 315 9)) &&
    (allLt (sG.map (unpackP 315 9)).size fun k =>
      j2InP (sG.map (unpackP 315 9))[k]! ||
        j2InP (compA 315 outerArr (sG.map (unpackP 315 9))[k]!)) &&
    (cS.toMain 315 9).pts.size == 256

@[expose] noncomputable def j2CheckWExc (e0 : Array (Array ℕ)) (sG roots : Array ℕ)
    (nodes : Array NodeP) (cS : ArrCertP) (wcs : Array (Array ArrCertP)) (excs : List ExcRefP) :
    Bool :=
  censusExcOKW 315 j2PS j2InP j2InP j2InR false false false (sG.map (unpackP 315 9)) roots
      (nodes.map (NodeP.toMain 315 9)) (cS.toMain 315 9)
      (wcs.map fun cs => cs.map (ArrCertP.toMain 315 9)) e0 (excs.map (ExcRefP.toMain 315 9)) &&
    (allLt (sG.map (unpackP 315 9)).size fun k =>
      j2InP (sG.map (unpackP 315 9))[k]! ||
        j2InP (compA 315 outerArr (sG.map (unpackP 315 9))[k]!)) &&
    (cS.toMain 315 9).pts.size == 256

end CFSG.ComponentClassification.RankTwoSporadic.J2
