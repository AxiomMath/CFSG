module

public import Certificates.Data.Kernel.Census.PackedConj
public import CFSG.Certificates.Kernel.Census.ToMainExc
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicConjW

public section

namespace CFSG.KC.Census

open CFSG.ComponentClassification.RankTwoSporadic.Cert

variable (n w : Nat)

@[expose] noncomputable def ConjDataP.toMain (d : ConjDataP) : ConjData :=
  ⟨d.xs.map (unpackP n w), d.rs, d.cjs, d.bs, d.us.map (unpackP n w), d.im, d.wt, d.cm,
    d.cs.map (unpackP n w), d.ci.map (unpackP n w), d.roots, d.nodes.map (NodeP.toMain n w),
    d.ents, d.wcs.map fun cs => cs.map (ArrCertP.toMain n w), d.excs.map (ExcRefP.toMain n w)⟩

@[expose] def canonC (d : ConjDataP) : Bool :=
  d.xs.all (canon1 n w) && d.us.toList.all (canon1 n w) && d.cs.toList.all (canon1 n w) &&
    d.ci.toList.all (canon1 n w) &&
    d.nodes.toList.all (fun nd => nd.basis.toList.all (canon1 n w) && canonW n w nd.wit) &&
    d.wcs.toList.all (fun cs => cs.toList.all fun c => c.pts.toList.all (canon1 n w)) &&
    d.excs.all fun r => canon1 n w r.w

end CFSG.KC.Census
