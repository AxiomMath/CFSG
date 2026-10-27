module

public import Certificates.Data.Kernel.Census.PackedF
public import CFSG.Certificates.Kernel.Census.ToMain
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ1Full

public section

namespace CFSG.KC.Census

open CFSG.ComponentClassification.RankTwoSporadic.Cert

variable (n w : Nat)

@[expose] noncomputable def FNodeP.toMain (nd : FNodeP) : FNode :=
  ⟨nd.basis.map (unpackP n w), nd.facs.map (NFacP.toMain n w), nd.prog, nd.gIdx⟩

@[expose] def canonF (nodes : Array FNodeP) : Bool :=
  nodes.toList.all fun nd => nd.basis.toList.all (canon1 n w) && nd.facs.all fun f => canonG n w f.γ

end CFSG.KC.Census
