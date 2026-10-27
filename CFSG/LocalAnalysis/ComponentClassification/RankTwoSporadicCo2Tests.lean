module

public import CFSG.Sporadic.Co2Schreier.Arrays
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Census

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co2

open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.ComponentClassification.RankTwoSporadic.RootCensus
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Co2Cert
  CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Schreier.Tits

@[expose] def co2UArr : Array ℕ := compA 2300 sArrs[8]! sArrs[0]!

@[expose] def co2Xs : List (Array ℕ) := [zArr, tArr, co2UArr]

end CFSG.ComponentClassification.RankTwoSporadic.Co2
