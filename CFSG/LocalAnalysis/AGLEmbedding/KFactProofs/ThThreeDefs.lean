module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TcGenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointDefs

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

@[expose] def thSlpFacts : List MFact :=
  [.ord 0 2, .ord 1 3,
   .ord 2 19, .eq [(2, 1)] [(0, 1), (1, 1)],
   .ord 3 19, .eq [(3, 1)] [(2, 1), (1, 1)],
   .ord 4 10, .eq [(4, 1)] [(2, 1), (3, 1)],
   .ord 5 18, .eq [(5, 1)] [(2, 1), (4, 1)],
   .ord 6 3, .eq [(6, 1)] [(0, 1), (5, 1)],
   .ord 7 3, .eq [(7, 1)] [(5, 1), (0, 1)],
   .ord 8 3, .eq [(8, 1)] [(7, 2)],
   .ord 9 19, .eq [(9, 1)] [(8, 1), (6, 1)],
   .ord 10 18, .eq [(10, 1)] [(5, 1), (4, 1)],
   .ord 11 19, .eq [(11, 1)] [(2, 1), (10, 1)],
   .ord 12 24, .eq [(12, 1)] [(11, 1), (3, 1)],
   .ord 13 19, .eq [(13, 1)] [(0, 1), (12, 1)],
   .ord 14 19, .eq [(14, 1)] [(12, 1), (0, 1)],
   .ord 15 19, .eq [(15, 1)] [(14, 18)],
   .ord 16 28, .eq [(16, 1)] [(15, 1), (13, 1)],
   .ord 17 2, .eq [(17, 1)] [(16, 14)],
   .ord 18 19, .eq [(18, 1)] [(9, 9)],
   .ord 19 6, .eq [(19, 1)] [(6, 1), (18, 1)]]

structure ZGen where
  rg : Nat
  og : Nat
  rt2 : Nat
  rx2 : Nat
  ry2 : Nat
  tne : Nat
  wx : Word
  wy : Word
  wx2 : Word
  wy2 : Word
deriving Inhabited

@[expose] def ZGen.facts (G : ZGen) : List MFact :=
  [.ord G.rg G.og, .ord G.rt2 2, .ord G.rx2 2, .ord G.ry2 6,
   .conj G.rg [(0, 1)] [(G.rt2, 1)], .conj G.rg [(17, 1)] [(G.rx2, 1)],
   .conj G.rg [(19, 1)] [(G.ry2, 1)], .ne [(0, 1)] [(G.rt2, 1)] G.tne,
   .eq [(17, 1)] G.wx, .eq [(19, 1)] G.wy, .eq [(G.rx2, 1)] G.wx2, .eq [(G.ry2, 1)] G.wy2]

@[expose] def ZGen.words (G : ZGen) : Word := G.wx ++ G.wy ++ G.wx2 ++ G.wy2

structure TZSpec where
  p : Nat
  pc : List Pc
  subs : List TSub
  gen : ZGen
deriving Inhabited

@[expose] def TZSpec.facts (D : TZSpec) : List MFact :=
  thSlpFacts ++ D.pc.flatMap (Pc.facts D.p) ++ D.subs.flatMap (TSub.facts D.p) ++ D.gen.facts

@[expose] def TZSpec.actRegs (D : TZSpec) : List Nat :=
  D.subs.flatMap fun s => s.acts.map (·.reg)

@[expose] def TSub.wfIn (p : Nat) (pc : List Pc) (s : TSub) : Bool :=
  s.gens.all (fun u => u.w.all fun a => pc.any (·.reg == a.1)) &&
  s.genWord s.v0 && s.genWord s.v1 &&
  s.v2.all (fun a => pc.any (·.reg == a.1)) &&
  (nonzeroTriples p).all (fun v => s.indep.any fun q =>
    q.1 == v.1 && q.2.1 == v.2.1 && q.2.2.1 == v.2.2) &&
  s.acts.all (fun g =>
    g.imgs.all (fun c => s.gens.any (·.reg == c.1) && s.genWord c.2) &&
    s.gens.all fun u => g.imgs.any (·.1 == u.reg))

@[expose] def TZSpec.wf (D : TZSpec) : Bool :=
  decide (2 ≤ D.p) && pcWf D.pc && D.subs.all (TSub.wfIn D.p D.pc) &&
  D.gen.words.all (fun q => D.actRegs.contains q.1)

@[expose] def tzCheck {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (nregs : Nat)
    (prog : List Op) (D : TZSpec) : Bool :=
  mcertCheck O sA sB ⟨nregs, prog, D.facts⟩ &&
  O.eq (O.regsOf sA sB nregs prog)[0]! (O.decode sA) &&
  O.eq (O.regsOf sA sB nregs prog)[1]! (O.decode sB) && D.wf

structure CZSpec where
  p : Nat
  m : Mod
  pts : List CpPt
  gen : ZGen
deriving Inhabited

@[expose] def CZSpec.facts (D : CZSpec) : List MFact :=
  thSlpFacts ++ Mod.facts D.p D.m ++ D.pts.flatMap (CpPt.facts D.p) ++ D.gen.facts

@[expose] def CZSpec.actRegs (D : CZSpec) : List Nat :=
  D.m.acts.map (·.reg) ++ D.pts.flatMap fun b => b.hs.map (·.reg)

@[expose] def CZSpec.wf (D : CZSpec) : Bool :=
  decide (2 ≤ D.p) &&
  D.pts.all (fun b => b.w.all fun a => a.1 == D.m.b0 || a.1 == D.m.b1 || a.1 == D.m.b2) &&
  (nonzeroTriples D.p).all (fun v => D.m.indep.any fun q =>
    q.1 == v.1 && q.2.1 == v.2.1 && q.2.2.1 == v.2.2) &&
  D.gen.words.all (fun q => D.actRegs.contains q.1)

@[expose] def CZSpec.noFun (D : CZSpec) : Bool :=
  (nonzeroTriples D.p).all fun v => D.m.acts.any fun g => !g.fixesVec D.p v.1 v.2.1 v.2.2

@[expose] def czCheck {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (nregs : Nat)
    (prog : List Op) (D : CZSpec) : Bool :=
  mcertCheck O sA sB ⟨nregs, prog, D.facts⟩ &&
  O.eq (O.regsOf sA sB nregs prog)[0]! (O.decode sA) &&
  O.eq (O.regsOf sA sB nregs prog)[1]! (O.decode sB) && D.noFun && D.wf

end CFSG.AGLEmbedding.R3
