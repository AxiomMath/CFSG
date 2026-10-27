module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzTests
public import CFSG.Certificates.Kernel.Census.ToMainConj

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Suz

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.SuzOddCore CFSG.KC.Census

@[expose] noncomputable def suzXsOK (d : ConjDataP) : Bool :=
  (d.toMain 1782 11).xs.all (fun a => suzInM a || suzInM (compA 1782 vArr a)) &&
    (d.toMain 1782 11).xs.length == 14

@[expose] noncomputable def suzCheckWII (d : ConjDataP) : Bool :=
  conjCensusOKW 1782 suzPS suzInM suzInM suzInT false true false (d.toMain 1782 11) #[] &&
    suzXsOK d

@[expose] noncomputable def suzCheckWExc (e0 : Array (Array ℕ)) (d : ConjDataP) : Bool :=
  conjCensusOKW 1782 suzPS suzInM suzInM suzInT false false false (d.toMain 1782 11) e0 &&
    suzXsOK d

end CFSG.ComponentClassification.RankTwoSporadic.Suz
