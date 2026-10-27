module

public import Certificates.Data.CFSGNative.Fi23.Certificate
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Census

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Fi23

open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.ComponentClassification.RankTwoSporadic.RootCensus
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Tits

@[expose] def fi23Gens : Array (Array ℕ) :=
  let o := CFSG.Sporadic.Fi23.Native.orbitData ()
  #[o.alpha.map UInt32.toNat, o.beta.map UInt32.toNat]

@[expose] def fi23Fix : List ℕ := [3511, 695, 183]

end CFSG.ComponentClassification.RankTwoSporadic.Fi23
