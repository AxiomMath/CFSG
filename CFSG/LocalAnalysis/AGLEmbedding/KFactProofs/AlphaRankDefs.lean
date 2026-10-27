module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.DerDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.RankThreeDefs

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

structure RMod where
  nm : NMod
  ws : List Word
deriving Inhabited

structure RLin where
  cf : Nat → Nat → Nat → Int
  ci : Nat → Nat → Nat → Nat → Nat → Int
  ct : Nat → Nat → Nat → Nat → Int
deriving Inhabited

structure RSpec where
  p : Nat
  pc : List Pc
  mods : List RMod
  ders : List Der
  rA : Nat
  oA : Nat
  rB : Nat
  oB : Nat
  wA : Word
  wB : Word
deriving Inhabited

@[expose] def RMod.facts (p : Nat) (m : RMod) : List MFact :=
  m.nm.facts p ++ (List.range m.nm.basis.length).map fun k =>
    MFact.eq [(m.nm.basis.getD k 0, 1)] (m.ws.getD k [])

@[expose] def RSpec.facts (D : RSpec) : List MFact :=
  [.ord D.rA D.oA, .ord D.rB D.oB, .eq [(D.rA, 1)] D.wA, .eq [(D.rB, 1)] D.wB] ++
  D.pc.flatMap (Pc.facts D.p) ++ D.mods.flatMap (RMod.facts D.p) ++ D.ders.flatMap Der.facts

@[expose] def RSpec.actRegs (D : RSpec) : List Nat :=
  D.mods.flatMap fun m => m.nm.acts.map (·.reg)

@[expose] def RSpec.wf (D : RSpec) : Bool :=
  decide (2 ≤ D.p) && pcWf D.pc &&
  D.mods.all (fun m => m.nm.wf D.p && decide (2 ≤ m.nm.basis.length) &&
    decide (m.ws.length = m.nm.basis.length) &&
    m.ws.all fun w => w.all fun a => D.pc.any (·.reg == a.1)) &&
  derWf D.actRegs D.ders &&
  (D.wA ++ D.wB).all fun q => (D.ders.map (·.reg) ++ D.actRegs).contains q.1

@[expose] def RSpec.linOK (D : RSpec) (tabs : List RLin) : Bool :=
  decide (tabs.length = D.mods.length) &&
  (List.range D.mods.length).all fun i =>
    (D.mods.getD i default).nm.altOK D.p (tabs.getD i default).ci (tabs.getD i default).ct tgtAlt &&
    (decide (3 ≤ (D.mods.getD i default).nm.basis.length) ||
      (D.mods.getD i default).nm.funOK D.p (tabs.getD i default).cf)

@[expose] def rlCheck {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (nregs : Nat)
    (prog : List Op) (D : RSpec) (tabs : List RLin) : Bool :=
  mcertCheck O sA sB ⟨nregs, prog, D.facts⟩ &&
  decide (D.rA < nregs) && decide (D.rB < nregs) &&
  O.eq (O.regsOf sA sB nregs prog)[D.rA]! (O.decode sA) &&
  O.eq (O.regsOf sA sB nregs prog)[D.rB]! (O.decode sB) && D.wf && D.linOK tabs

end CFSG.AGLEmbedding.R3
