module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.DerDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.RankThreeDefs

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

structure TGen where
  reg : Nat
  ord : Nat
  w : Word
deriving Inhabited

structure TAct where
  reg : Nat
  ord : Nat
  imgs : List (Nat × Word)
deriving Inhabited

structure TSub where
  gens : List TGen
  c0 : Nat
  c1 : Nat
  c2 : Nat
  v0 : Word
  v1 : Word
  v2 : Word
  indep : List (Nat × Nat × Nat × Nat)
  acts : List TAct
deriving Inhabited

structure TSpec where
  p : Nat
  pc : List Pc
  subs : List TSub
  rA : Nat
  oA : Nat
  rB : Nat
  oB : Nat
  wA : Word
  wB : Word
  der : List Der := []
deriving Inhabited

@[expose] def TSub.facts (p : Nat) (s : TSub) : List MFact :=
  s.gens.flatMap (fun u => [MFact.ord u.reg u.ord, MFact.eq [(u.reg, 1)] u.w]) ++
  [.ord s.c0 p, .ord s.c1 p, .ord s.c2 p, .eq [(s.c0, 1)] s.v0, .eq [(s.c1, 1)] s.v1,
    .eq [(s.c2, 1)] s.v2, .eq [(s.c0, 1), (s.c1, 1)] [(s.c1, 1), (s.c0, 1)],
    .eq [(s.c0, 1), (s.c2, 1)] [(s.c2, 1), (s.c0, 1)],
    .eq [(s.c1, 1), (s.c2, 1)] [(s.c2, 1), (s.c1, 1)]] ++
  s.gens.map (fun u => MFact.eq [(s.c2, 1), (u.reg, 1)] [(u.reg, 1), (s.c2, 1)]) ++
  s.indep.map (fun v =>
    MFact.ne [(s.c0, v.1), (s.c1, v.2.1), (s.c2, v.2.2.1)] [] v.2.2.2) ++
  s.acts.flatMap (fun g => MFact.ord g.reg g.ord ::
    g.imgs.map (fun c => MFact.conj g.reg [(c.1, 1)] c.2))

@[expose] def TSpec.facts (D : TSpec) : List MFact :=
  [.ord D.rA D.oA, .ord D.rB D.oB, .eq [(D.rA, 1)] D.wA, .eq [(D.rB, 1)] D.wB] ++
  D.pc.flatMap (Pc.facts D.p) ++ D.subs.flatMap (TSub.facts D.p) ++ D.der.flatMap Der.facts

@[expose] def TSpec.actRegs (D : TSpec) : List Nat :=
  D.subs.flatMap fun s => s.acts.map (·.reg)

@[expose] def TSub.genWord (s : TSub) (w : Word) : Bool :=
  w.all fun a => s.gens.any (·.reg == a.1)

@[expose] def TSpec.wf (D : TSpec) : Bool :=
  decide (2 ≤ D.p) && pcWf D.pc &&
  D.subs.all (fun s =>
    s.gens.all (fun u => u.w.all fun a => D.pc.any (·.reg == a.1)) &&
    s.genWord s.v0 && s.genWord s.v1 &&
    s.v2.all (fun a => D.pc.any (·.reg == a.1)) &&
    (nonzeroTriples D.p).all (fun v => s.indep.any fun q =>
      q.1 == v.1 && q.2.1 == v.2.1 && q.2.2.1 == v.2.2) &&
    s.acts.all (fun g =>
      g.imgs.all (fun c => s.gens.any (·.reg == c.1) && s.genWord c.2) &&
      s.gens.all fun u => g.imgs.any (·.1 == u.reg))) &&
  derWf D.actRegs D.der &&
  (D.wA ++ D.wB).all (fun q => (D.actRegs ++ D.der.map (·.reg)).contains q.1)

@[expose] def tcCheck {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (nregs : Nat)
    (prog : List Op) (D : TSpec) : Bool :=
  mcertCheck O sA sB ⟨nregs, prog, D.facts⟩ &&
  decide (D.rA < nregs) && decide (D.rB < nregs) &&
  O.eq (O.regsOf sA sB nregs prog)[D.rA]! (O.decode sA) &&
  O.eq (O.regsOf sA sB nregs prog)[D.rB]! (O.decode sB) && D.wf

@[expose] def tcCheckHead {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (nregs : Nat)
    (prog : List Op) (D : TSpec) (m : Nat) : Bool :=
  mcertCheck O sA sB ⟨nregs, prog, D.facts.take m⟩ &&
  decide (D.rA < nregs) && decide (D.rB < nregs) &&
  O.eq (O.regsOf sA sB nregs prog)[D.rA]! (O.decode sA) &&
  O.eq (O.regsOf sA sB nregs prog)[D.rB]! (O.decode sB) && D.wf

@[expose] def tcCheckTail {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (nregs : Nat)
    (prog : List Op) (D : TSpec) (m : Nat) : Bool :=
  mcertCheck O sA sB ⟨nregs, prog, D.facts.drop m⟩

end CFSG.AGLEmbedding.R3
