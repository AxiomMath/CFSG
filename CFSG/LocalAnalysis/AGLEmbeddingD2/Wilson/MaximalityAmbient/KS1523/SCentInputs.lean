module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check45Inputs

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523

open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover
  CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Mathieu

@[expose] def sCentOK : Bool :=
  (List.range 3).all fun k => (List.range 64).all fun i =>
    !(commA (cS k).pts[i]! zArr) || (List.range 64).all fun j => commA (cS k).pts[i]! (cS k).pts[j]!

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523
