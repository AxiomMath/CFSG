module

public import Certificates.Data.Kernel.Census.PackedRoot
public import CFSG.Certificates.Kernel.Census.ToMain
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Census

public section

namespace CFSG.KC.Census

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.ComponentClassification.RankTwoSporadic.RootCensus
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

variable (n w : Nat)

@[expose] def canonWitP : RootWitP → Bool
  | .ord4c _ c₁ c₂ _ => canon1 n w c₁ && canon1 n w c₂
  | _ => true

@[expose] def canonR (r : RootConjP) : Bool :=
  canon1 n w r.x && r.xs.all (canon1 n w) && r.xi.all (canon1 n w) &&
    r.cs.toList.all (canon1 n w) &&
    r.ga.toList.all (canon1 n w) && r.gi.toList.all (canon1 n w) &&
    r.cands.toList.all (canonWitP n w) && r.kb.all (fun p => Nat.blt p n) &&
    r.perfs.toList.all fun P => P.cP.pts.toList.all (canon1 n w) &&
      P.cQ.pts.toList.all (canon1 n w) && P.cR.pts.toList.all (canon1 n w)

end CFSG.KC.Census
