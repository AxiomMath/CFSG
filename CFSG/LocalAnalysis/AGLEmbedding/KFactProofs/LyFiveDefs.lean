module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.LyThreeDefs

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

structure HEl where
  reg : Nat
  ord : Nat
  w : Word
deriving Inhabited, DecidableEq

structure HGen where
  els : List HEl
  rs : Nat
  os : Nat
deriving Inhabited

@[expose] def HGen.facts (G : HGen) : List MFact :=
  [.ord 0 2, .ord 1 5, .ord G.rs G.os] ++
    G.els.flatMap fun e => [.ord e.reg e.ord, .eq [(e.reg, 1)] e.w]

@[expose] def HGen.words (G : HGen) : Word := G.els.flatMap (·.w) ++ [(G.rs, 1)]

structure L5ZSpec where
  p : Nat
  pc : List Pc
  subs : List TSub
  gen : HGen
deriving Inhabited

@[expose] def L5ZSpec.facts (D : L5ZSpec) : List MFact :=
  D.pc.flatMap (Pc.facts D.p) ++ D.subs.flatMap (TSub.facts D.p) ++ D.gen.facts

@[expose] def L5ZSpec.actRegs (D : L5ZSpec) : List Nat :=
  D.subs.flatMap fun s => s.acts.map (·.reg)

@[expose] def L5ZSpec.wf (D : L5ZSpec) : Bool :=
  decide (2 ≤ D.p) && pcWf D.pc && D.subs.all (TSub.lyWf D.p D.pc) &&
  D.gen.words.all (fun q => D.actRegs.contains q.1)

structure L5CSpec where
  p : Nat
  m : Mod
  pts : List CpPt
  gen : HGen
deriving Inhabited

@[expose] def L5CSpec.facts (D : L5CSpec) : List MFact :=
  Mod.facts D.p D.m ++ D.pts.flatMap (CpPt.facts D.p) ++ D.gen.facts

@[expose] def L5CSpec.actRegs (D : L5CSpec) : List Nat :=
  D.m.acts.map (·.reg) ++ D.pts.flatMap fun b => b.hs.map (·.reg)

@[expose] def L5CSpec.wf (D : L5CSpec) : Bool :=
  decide (2 ≤ D.p) &&
  D.pts.all (fun b => b.w.all fun a => a.1 == D.m.b0 || a.1 == D.m.b1 || a.1 == D.m.b2) &&
  (nonzeroTriples D.p).all (fun v => D.m.indep.any fun q =>
    q.1 == v.1 && q.2.1 == v.2.1 && q.2.2.1 == v.2.2) &&
  D.gen.words.all (fun q => D.actRegs.contains q.1)

@[expose] def L5CSpec.noFun (D : L5CSpec) : Bool :=
  (nonzeroTriples D.p).all fun v => D.m.acts.any fun g => !g.fixesVec D.p v.1 v.2.1 v.2.2

@[expose] def ly5Check {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (aMats : List M)
    (stab : M → Bool) (nregs : Nat) (prog : List Op) (Dz : L5ZSpec) (Dc : L5CSpec) : Bool :=
  let R := O.regsOf sA sB nregs prog
  certOK O R ⟨nregs, prog, Dz.facts ++ Dc.facts⟩ &&
  O.eq R[0]! (O.decode sA) && O.eq R[1]! (O.decode sB) &&
  decide (Dz.gen.els.length = 5) && decide (aMats.length = 5) &&
  (List.range 5).all (fun j => O.eq R[(Dz.gen.els.getD j default).reg]! (aMats.getD j default)) &&
  stab R[Dz.gen.rs]! && decide (Dc.gen.els = Dz.gen.els ∧ Dc.gen.rs = Dz.gen.rs) &&
  Dc.noFun && Dz.wf && Dc.wf

end CFSG.AGLEmbedding.R3
