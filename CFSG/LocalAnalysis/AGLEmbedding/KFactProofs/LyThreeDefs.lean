module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TcGenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointDefs

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

structure LGen where
  rc0 : Nat
  rc1 : Nat
  wc0 : Word
  wc1 : Word
  rl : Nat
  ol : Nat
  rt : Nat
  tne : Nat
deriving Inhabited

@[expose] def LGen.facts (G : LGen) : List MFact :=
  [.ord 0 2, .ord 1 5, .ord G.rc0 14, .ord G.rc1 6, .eq [(G.rc0, 1)] G.wc0,
   .eq [(G.rc1, 1)] G.wc1, .ord G.rl G.ol, .ord G.rt 2, .conj G.rl [(0, 1)] [(G.rt, 1)],
   .eq [(G.rt, 1), (0, 1)] [(0, 1), (G.rt, 1)], .ne [(0, 1)] [(G.rt, 1)] G.tne]

@[expose] def LGen.words (G : LGen) : Word := G.wc0 ++ G.wc1 ++ [(G.rl, 1)]

structure LZSpec where
  p : Nat
  pc : List Pc
  subs : List TSub
  gen : LGen
deriving Inhabited

@[expose] def LZSpec.facts (D : LZSpec) : List MFact :=
  D.pc.flatMap (Pc.facts D.p) ++ D.subs.flatMap (TSub.facts D.p) ++ D.gen.facts

@[expose] def LZSpec.actRegs (D : LZSpec) : List Nat :=
  D.subs.flatMap fun s => s.acts.map (·.reg)

@[expose] def TSub.lyWf (p : Nat) (pc : List Pc) (s : TSub) : Bool :=
  s.gens.all (fun u => u.w.all fun a => pc.any (·.reg == a.1)) &&
  s.genWord s.v0 && s.genWord s.v1 &&
  s.v2.all (fun a => pc.any (·.reg == a.1)) &&
  (nonzeroTriples p).all (fun v => s.indep.any fun q =>
    q.1 == v.1 && q.2.1 == v.2.1 && q.2.2.1 == v.2.2) &&
  s.acts.all (fun g =>
    g.imgs.all (fun c => s.gens.any (·.reg == c.1) && s.genWord c.2) &&
    s.gens.all fun u => g.imgs.any (·.1 == u.reg))

@[expose] def LZSpec.wf (D : LZSpec) : Bool :=
  decide (2 ≤ D.p) && pcWf D.pc && D.subs.all (TSub.lyWf D.p D.pc) &&
  D.gen.words.all (fun q => D.actRegs.contains q.1)

structure LCSpec where
  p : Nat
  m : Mod
  pts : List CpPt
  gen : LGen
deriving Inhabited

@[expose] def LCSpec.facts (D : LCSpec) : List MFact :=
  Mod.facts D.p D.m ++ D.pts.flatMap (CpPt.facts D.p) ++ D.gen.facts

@[expose] def LCSpec.actRegs (D : LCSpec) : List Nat :=
  D.m.acts.map (·.reg) ++ D.pts.flatMap fun b => b.hs.map (·.reg)

@[expose] def LCSpec.wf (D : LCSpec) : Bool :=
  decide (2 ≤ D.p) &&
  D.pts.all (fun b => b.w.all fun a => a.1 == D.m.b0 || a.1 == D.m.b1 || a.1 == D.m.b2) &&
  (nonzeroTriples D.p).all (fun v => D.m.indep.any fun q =>
    q.1 == v.1 && q.2.1 == v.2.1 && q.2.2.1 == v.2.2) &&
  D.gen.words.all (fun q => D.actRegs.contains q.1)

@[expose] def LCSpec.noFun (D : LCSpec) : Bool :=
  (nonzeroTriples D.p).all fun v => D.m.acts.any fun g => !g.fixesVec D.p v.1 v.2.1 v.2.2

@[expose] def certOK {M V : Type} [Inhabited M] (O : Ops M V) (R : Array M) (C : MCert) : Bool :=
  decide (2 ≤ C.nregs) && C.prog.all (Op.lt C.nregs) && C.facts.all (factOK O R C.nregs)

theorem mcertCheck_eq_certOK {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String)
    (C : MCert) : mcertCheck O sA sB C = certOK O (O.regsOf sA sB C.nregs C.prog) C := rfl

@[expose] def lyCheck {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (c0 c1 : M)
    (nregs : Nat) (prog : List Op) (Dz : LZSpec) (Dc : LCSpec) : Bool :=
  let R := O.regsOf sA sB nregs prog
  certOK O R ⟨nregs, prog, Dz.facts ++ Dc.facts⟩ &&
  O.eq R[0]! (O.decode sA) && O.eq R[1]! (O.decode sB) && O.eq R[Dz.gen.rc0]! c0 &&
  O.eq R[Dz.gen.rc1]! c1 && decide (Dc.gen.rc0 = Dz.gen.rc0 ∧ Dc.gen.rc1 = Dz.gen.rc1) &&
  Dc.noFun && Dz.wf && Dc.wf

end CFSG.AGLEmbedding.R3
