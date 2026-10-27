module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.DerDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.RankThreeDefs

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

structure CpH where
  reg : Nat
  ord : Nat
  e : Nat
deriving Inhabited

structure CpPt where
  reg : Nat
  w : Word
  t : Nat
  hs : List CpH
deriving Inhabited

structure CpSpec where
  p : Nat
  m : Mod
  pts : List CpPt
  rA : Nat
  oA : Nat
  rB : Nat
  oB : Nat
  wA : Word
  wB : Word
  der : List Der := []
deriving Inhabited

@[expose] def CpPt.facts (p : Nat) (b : CpPt) : List MFact :=
  [.ord b.reg p, .eq [(b.reg, 1)] b.w, .ne [(b.reg, 1)] [] b.t] ++
  b.hs.flatMap (fun h => [MFact.ord h.reg h.ord, MFact.conj h.reg [(b.reg, 1)] [(b.reg, h.e)]])

@[expose] def CpSpec.facts (D : CpSpec) : List MFact :=
  [.ord D.rA D.oA, .ord D.rB D.oB, .eq [(D.rA, 1)] D.wA, .eq [(D.rB, 1)] D.wB] ++
  Mod.facts D.p D.m ++ D.pts.flatMap (CpPt.facts D.p) ++ D.der.flatMap Der.facts

@[expose] def CpSpec.actRegs (D : CpSpec) : List Nat :=
  D.m.acts.map (·.reg) ++ D.pts.flatMap fun b => b.hs.map (·.reg)

@[expose] def CpSpec.wf (D : CpSpec) : Bool :=
  decide (2 ≤ D.p) &&
  D.pts.all (fun b => b.w.all fun a => a.1 == D.m.b0 || a.1 == D.m.b1 || a.1 == D.m.b2) &&
  (nonzeroTriples D.p).all (fun v => D.m.indep.any fun q =>
    q.1 == v.1 && q.2.1 == v.2.1 && q.2.2.1 == v.2.2) &&
  derWf D.actRegs D.der &&
  (D.wA ++ D.wB).all (fun q => (D.actRegs ++ D.der.map (·.reg)).contains q.1)

@[expose] def CpSpec.noFun (D : CpSpec) : Bool :=
  (nonzeroTriples D.p).all fun v => D.m.acts.any fun g => !g.fixesVec D.p v.1 v.2.1 v.2.2

@[expose] def cpCheck {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (nregs : Nat)
    (prog : List Op) (D : CpSpec) : Bool :=
  mcertCheck O sA sB ⟨nregs, prog, D.facts⟩ &&
  decide (D.rA < nregs) && decide (D.rB < nregs) &&
  O.eq (O.regsOf sA sB nregs prog)[D.rA]! (O.decode sA) &&
  O.eq (O.regsOf sA sB nregs prog)[D.rB]! (O.decode sB) && D.wf

end CFSG.AGLEmbedding.R3
