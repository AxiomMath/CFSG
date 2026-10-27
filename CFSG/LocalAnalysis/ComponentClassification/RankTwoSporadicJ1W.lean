module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ1Tests
public import CFSG.Certificates.Kernel.Census.ToMainF
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFullW

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J1

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KC.Census

@[expose] noncomputable def j1CheckW (prog : List (ℕ × ℕ)) (sG : Array ℕ) (nodes : Array FNodeP)
    (cS : ArrCertP) : Bool :=
  slpOK 3080 j1Gens prog &&
    fCensusOKW 3080 j1PS (inRegsL 3080 (slpRegs 3080 j1Gens prog)) j1Gens
      (sG.map (unpackP 3080 12)) (nodes.map (FNodeP.toMain 3080 12)) (cS.toMain 3080 12) &&
    (allLt (sG.map (unpackP 3080 12)).size fun k =>
      inRegsL 3080 (slpRegs 3080 j1Gens prog) (sG.map (unpackP 3080 12))[k]!) &&
    (cS.toMain 3080 12).pts.size == 8

end CFSG.ComponentClassification.RankTwoSporadic.J1
