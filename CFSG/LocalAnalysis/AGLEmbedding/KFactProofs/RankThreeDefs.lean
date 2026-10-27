module

public import CFSG.RankThree.Asc83Table.MatCertDefs

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

structure Pc where
  reg : Nat
  ord : Nat
  pw : Word
  cj : List (Nat × Word)
deriving Inhabited

structure Act where
  reg : Nat
  ord : Nat
  mat : List Nat
deriving Inhabited

structure Mod where
  b0 : Nat
  b1 : Nat
  b2 : Nat
  w0 : Word
  w1 : Word
  w2 : Word
  indep : List (Nat × Nat × Nat × Nat)
  acts : List Act
deriving Inhabited

structure Spec where
  p : Nat
  pc : List Pc
  mods : List Mod
  rA : Nat
  oA : Nat
  rB : Nat
  oB : Nat
  wA : Word
  wB : Word
deriving Inhabited

@[expose] def nonzeroTriples (p : Nat) : List (Nat × Nat × Nat) :=
  ((List.range p).flatMap fun a => (List.range p).flatMap fun b =>
    (List.range p).map fun c => (a, b, c)).filter fun v => !(v.1 == 0 && v.2.1 == 0 && v.2.2 == 0)

@[expose] def Mod.word (m : Mod) (a b c : Nat) : Word := [(m.b0, a), (m.b1, b), (m.b2, c)]

@[expose] def Mod.col (m : Mod) (g : Act) (i : Nat) : Word :=
  [(m.b0, g.mat.getD i 0), (m.b1, g.mat.getD (3 + i) 0), (m.b2, g.mat.getD (6 + i) 0)]

@[expose] def Mod.basis (m : Mod) : Nat → Nat
  | 0 => m.b0
  | 1 => m.b1
  | _ => m.b2

@[expose] def Pc.facts (p : Nat) (q : Pc) : List MFact :=
  [.ord q.reg q.ord, .eq [(q.reg, p)] q.pw] ++
    q.cj.map (fun c => MFact.conj q.reg [(c.1, 1)] c.2)

@[expose] def Mod.facts (p : Nat) (m : Mod) : List MFact :=
  [.ord m.b0 p, .ord m.b1 p, .ord m.b2 p, .eq [(m.b0, 1)] m.w0, .eq [(m.b1, 1)] m.w1,
    .eq [(m.b2, 1)] m.w2, .eq [(m.b0, 1), (m.b1, 1)] [(m.b1, 1), (m.b0, 1)],
    .eq [(m.b0, 1), (m.b2, 1)] [(m.b2, 1), (m.b0, 1)],
    .eq [(m.b1, 1), (m.b2, 1)] [(m.b2, 1), (m.b1, 1)]] ++
  m.indep.map (fun v => MFact.ne (m.word v.1 v.2.1 v.2.2.1) [] v.2.2.2) ++
  m.acts.flatMap (fun g => [MFact.ord g.reg g.ord] ++
    [0, 1, 2].map (fun i => MFact.conj g.reg [(m.basis i, 1)] (m.col g i)))

@[expose] def Spec.facts (D : Spec) : List MFact :=
  [.ord D.rA D.oA, .ord D.rB D.oB, .eq [(D.rA, 1)] D.wA, .eq [(D.rB, 1)] D.wB] ++
  D.pc.flatMap (Pc.facts D.p) ++ D.mods.flatMap (Mod.facts D.p)

@[expose] def pcWf : List Pc → Bool
  | [] => true
  | q :: rest =>
    q.pw.all (fun a => rest.any (·.reg == a.1)) &&
    q.cj.all (fun c => rest.any (·.reg == c.1) && c.2.all fun a => rest.any (·.reg == a.1)) &&
    rest.all (fun r => q.cj.any (·.1 == r.reg)) && pcWf rest

@[expose] def Spec.wf (D : Spec) : Bool :=
  decide (2 ≤ D.p) && pcWf D.pc &&
  D.mods.all (fun m =>
    (m.w0 ++ m.w1 ++ m.w2).all (fun q => D.pc.any (·.reg == q.1)) &&
    (nonzeroTriples D.p).all (fun v => m.indep.any fun q =>
      q.1 == v.1 && q.2.1 == v.2.1 && q.2.2.1 == v.2.2)) &&
  (D.wA ++ D.wB).all (fun q => D.mods.any fun m => m.acts.any fun g => g.reg == q.1)

@[expose] def r3Check {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (nregs : Nat)
    (prog : List Op) (D : Spec) : Bool :=
  mcertCheck O sA sB ⟨nregs, prog, D.facts⟩ &&
  decide (D.rA < nregs) && decide (D.rB < nregs) &&
  O.eq (O.regsOf sA sB nregs prog)[D.rA]! (O.decode sA) &&
  O.eq (O.regsOf sA sB nregs prog)[D.rB]! (O.decode sB) && D.wf

@[expose] def Act.formEntry (g : Act) (a b c : Int) (i j : Nat) : Int :=
  let m : Nat → Nat → Int := fun k l => (g.mat.getD (3 * k + l) 0 : Nat)
  m 0 i * (a * m 1 j + b * m 2 j) + m 1 i * (-a * m 0 j + c * m 2 j) +
    m 2 i * (-b * m 0 j - c * m 1 j)

@[expose] def Act.fixes (p : Nat) (g : Act) (a b c : Nat) : Bool :=
  (g.formEntry a b c 0 1 - a) % (p : Int) == 0 && (g.formEntry a b c 0 2 - b) % (p : Int) == 0 &&
    (g.formEntry a b c 1 2 - c) % (p : Int) == 0

@[expose] def Act.fixesVec (p : Nat) (g : Act) (a b c : Nat) : Bool :=
  let m : Nat → Nat → Int := fun k l => (g.mat.getD (3 * k + l) 0 : Nat)
  (a * m 0 0 + b * m 1 0 + c * m 2 0 - a) % (p : Int) == 0 &&
    (a * m 0 1 + b * m 1 1 + c * m 2 1 - b) % (p : Int) == 0 &&
    (a * m 0 2 + b * m 1 2 + c * m 2 2 - c) % (p : Int) == 0

@[expose] def Spec.noAlt (D : Spec) : Bool :=
  D.mods.all fun m => (nonzeroTriples D.p).all fun v =>
    m.acts.any fun g => !g.fixes D.p v.1 v.2.1 v.2.2

end CFSG.AGLEmbedding.R3
