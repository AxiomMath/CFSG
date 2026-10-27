module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRankDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.LyFiveDefs

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

structure RLySpec where
  p : Nat
  pc : List Pc
  mods : List RMod
  ders : List Der
  gen : HGen
deriving Inhabited

@[expose] def RLySpec.facts (D : RLySpec) : List MFact :=
  D.pc.flatMap (Pc.facts D.p) ++ D.mods.flatMap (RMod.facts D.p) ++ D.ders.flatMap Der.facts ++
    D.gen.facts

@[expose] def RLySpec.actRegs (D : RLySpec) : List Nat :=
  D.mods.flatMap fun m => m.nm.acts.map (·.reg)

@[expose] def RLySpec.wf (D : RLySpec) : Bool :=
  decide (2 ≤ D.p) && pcWf D.pc &&
  D.mods.all (fun m => m.nm.wf D.p && decide (2 ≤ m.nm.basis.length) &&
    decide (m.ws.length = m.nm.basis.length) &&
    m.ws.all fun w => w.all fun a => D.pc.any (·.reg == a.1)) &&
  derWf D.actRegs D.ders &&
  D.gen.words.all fun q => (D.ders.map (·.reg) ++ D.actRegs).contains q.1

@[expose] def RLySpec.linOK (D : RLySpec) (tabs : List RLin) : Bool :=
  decide (tabs.length = D.mods.length) &&
  (List.range D.mods.length).all fun i =>
    (D.mods.getD i default).nm.altOK D.p (tabs.getD i default).ci (tabs.getD i default).ct tgtAlt &&
    (decide (3 ≤ (D.mods.getD i default).nm.basis.length) ||
      (D.mods.getD i default).nm.funOK D.p (tabs.getD i default).cf)

@[expose] def rlLyCheck {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (aMats : List M)
    (stab : M → Bool) (nregs : Nat) (prog : List Op) (D : RLySpec) (tabs : List RLin) : Bool :=
  let R := O.regsOf sA sB nregs prog
  certOK O R ⟨nregs, prog, D.facts⟩ &&
  O.eq R[0]! (O.decode sA) && O.eq R[1]! (O.decode sB) &&
  decide (D.gen.els.length = 5) && decide (aMats.length = 5) &&
  (List.range 5).all (fun j => O.eq R[(D.gen.els.getD j default).reg]! (aMats.getD j default)) &&
  stab R[D.gen.rs]! && D.wf && D.linOK tabs

end CFSG.AGLEmbedding.R3
