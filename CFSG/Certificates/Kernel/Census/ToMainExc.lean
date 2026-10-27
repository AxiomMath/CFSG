module

public import Certificates.Data.Kernel.Census.PackedExc
public import CFSG.Certificates.Kernel.Census.ToMain
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2Exc

public section

namespace CFSG.KC.Census

open CFSG.ComponentClassification.RankTwoSporadic.Cert

@[expose] noncomputable def ExcRefP.toMain (n w : Nat) (r : ExcRefP) : ExcRef :=
  ⟨r.node, unpackP n w r.w⟩

end CFSG.KC.Census
