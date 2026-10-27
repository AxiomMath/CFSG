module

public import Certificates.Data.Kernel.Census.Packed
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheckW2

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Monster.B.Fischer

variable (n w : Nat)

@[expose] noncomputable def unpackP (P : Nat) : Array Nat :=
  Array.ofFn (n := n) fun i => pg w (CFSG.KS.mask w) P i.val

@[expose] noncomputable def GFacP.toMain (f : GFacP) : GFac :=
  ⟨f.t, unpackP n w f.c₁, unpackP n w f.c₂⟩

@[expose] noncomputable def NFacP.toMain (f : NFacP) : NFac :=
  ⟨f.e, f.γ.map (GFacP.toMain n w)⟩

@[expose] noncomputable def CFacP.toMain (f : CFacP) : CFac :=
  ⟨unpackP n w f.x₁, unpackP n w f.x₂⟩

@[expose] noncomputable def WitP.toMain : WitP → Wit
  | .order4 l m => .order4 (l.map (NFacP.toMain n w)) m
  | .twoGroup gens k => .twoGroup (gens.map fun l => (l.1.map (NFacP.toMain n w), l.2)) k
  | .perfect gens comms x k conjs e g =>
    .perfect (gens.map fun l => (l.1.map (GFacP.toMain n w), l.2)) comms x k conjs e g
  | .inX => .inX
  | .small => .small
  | .closing s t c kc v gens comms =>
    .closing s t (unpackP n w c) kc v (gens.map fun l => (l.1.map (CFacP.toMain n w), l.2)) comms

@[expose] noncomputable def NodeP.toMain (nd : NodeP) : Node :=
  ⟨nd.basis.map (unpackP n w), nd.wit.toMain n w, nd.children⟩

@[expose] noncomputable def ArrCertP.toMain (c : ArrCertP) : ArrCert :=
  ⟨c.pts.map (unpackP n w), c.edges, c.par, c.lab⟩

@[expose] def PerfWP.toMain (pf : PerfWP) : PerfW :=
  ⟨pf.pw, pf.comms, pf.genQ, pf.x, pf.k, pf.conjs, pf.genR, pf.e, pf.g⟩

@[expose] def canon1 (P : Nat) : Bool := Nat.beq (Nat.shiftRight P (n * w)) 0

@[expose] def canonG (l : List GFacP) : Bool := l.all fun f => canon1 n w f.c₁ && canon1 n w f.c₂

@[expose] def canonW : WitP → Bool
  | .order4 l _ => l.all fun f => canonG n w f.γ
  | .twoGroup gens _ => gens.all fun l => l.1.all fun f => canonG n w f.γ
  | .perfect gens .. => gens.all fun l => canonG n w l.1
  | .closing _ _ c _ _ gens _ =>
    canon1 n w c && gens.all fun l => l.1.all fun f => canon1 n w f.x₁ && canon1 n w f.x₂
  | _ => true

@[expose] def canonP (sG : Array Nat) (nodes : Array NodeP) (cS : ArrCertP)
    (wcs : Array (Array ArrCertP)) : Bool :=
  sG.toList.all (canon1 n w) &&
    nodes.toList.all (fun nd => nd.basis.toList.all (canon1 n w) && canonW n w nd.wit) &&
    cS.pts.toList.all (canon1 n w) &&
    wcs.toList.all fun cs => cs.toList.all fun c => c.pts.toList.all (canon1 n w)

end CFSG.KC.Census
