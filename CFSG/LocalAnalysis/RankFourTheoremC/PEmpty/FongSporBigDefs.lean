module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMGenDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.RankThree.Asc83Table.Native CFSG.SectionRank.Native

@[expose] def MGen.checkBase {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (c : MGen) :
    Bool :=
  c.wf && mcertCheck O sA sB ⟨2, [], c.baseFacts⟩

structure PClaim where
  nregs : ℕ
  prog : List Op
  rz : ℕ
  rn : ℕ
  p : ℕ
  en : ℕ
  k : ℕ
  zt : ℕ

@[expose] def PClaim.facts (c : PClaim) : List MFact :=
  [.ord c.rz c.p, .ord c.rn c.en, .ne [(c.rz, 1)] [] c.zt, .conj c.rn [(c.rz, 1)] [(c.rz, c.k)]]

structure OClaim where
  nregs : ℕ
  prog : List Op
  rg : ℕ
  p : ℕ
  n : ℕ
  t : ℕ

@[expose] def OClaim.facts (c : OClaim) : List MFact :=
  [.ord c.rg (c.p ^ (c.n + 1)), .ne [(c.rg, c.p ^ c.n)] [] c.t]

@[expose] def OClaim.check {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (c : OClaim) :
    Bool :=
  decide c.p.Prime && mcertCheck O sA sB ⟨c.nregs, c.prog, c.facts⟩

@[expose] def PClaim.check {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (c : PClaim) :
    Bool :=
  decide c.p.Prime && mcertCheck O sA sB ⟨c.nregs, c.prog, c.facts⟩

structure BClaim where
  nregs : ℕ
  prog : List Op
  p : ℕ
  r : ℕ
  rz : ℕ
  rt : ℕ
  zt : ℕ
  tt : ℕ
  ws : List (ℕ × ℕ)
  zw : List (ℕ × ℕ)

@[expose] def BClaim.facts (c : BClaim) : List MFact :=
  [.ord c.rz c.p, .ne [(c.rz, 1)] [] c.zt, .ord c.rt 2, .ne [(c.rt, 1)] [] c.tt,
    .eq [(c.rz, 1), (c.rt, 1)] [(c.rt, 1), (c.rz, 1)], .eq [(c.rz, 1)] c.zw] ++
  c.ws.flatMap (fun q => [.ord q.1 c.r, .ne [(q.1, 1)] [] q.2,
    .eq [(q.1, 1), (c.rt, 1)] [(c.rt, 1), (q.1, 1)]])

@[expose] def BClaim.wf (c : BClaim) : Bool :=
  decide c.p.Prime && decide c.r.Prime &&
    c.zw.all (fun q => c.ws.any (fun w => decide (w.1 = q.1)))

@[expose] def BClaim.check {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (c : BClaim) :
    Bool :=
  c.wf && mcertCheck O sA sB ⟨c.nregs, c.prog, c.facts⟩

@[expose] def opTarget : Op → ℕ
  | .mul _ _ k => k
  | .pow _ _ k => k

structure GClaim where
  nregs : ℕ
  prog : List Op
  p : ℕ
  oa : ℕ
  ob : ℕ
  rz : ℕ
  zt : ℕ
  ts : List (ℕ × ℕ)
  ns : List (ℕ × ℕ × ℕ × ℕ)
  ms : List (ℕ × ℕ × ℕ)
  wa : List (ℕ × ℕ)
  wb : List (ℕ × ℕ)

@[expose] def GClaim.facts (c : GClaim) : List MFact :=
  [.ord 0 c.oa, .ord 1 c.ob, .ord c.rz c.p, .ne [(c.rz, 1)] [] c.zt, .eq [(0, 1)] c.wa,
    .eq [(1, 1)] c.wb] ++
  c.ts.flatMap (fun q => [.ord q.1 2, .ne [(q.1, 1)] [] q.2,
    .eq [(c.rz, 1), (q.1, 1)] [(q.1, 1), (c.rz, 1)]]) ++
  c.ns.flatMap (fun n => [.ord n.1 n.2.2.2, .eq [(n.1, 1), (c.rz, 1)] [(c.rz, n.2.1), (n.1, 1)],
    .eq [(n.1, 1), (c.rz, n.2.2.1)] [(c.rz, 1), (n.1, 1)]]) ++
  c.ms.flatMap (fun m => [.ord m.1 m.2.2,
    .eq [(m.1, 1), ((c.ts.getD m.2.1 (0, 0)).1, 1)] [((c.ts.getD m.2.1 (0, 0)).1, 1), (m.1, 1)]])

@[expose] def GClaim.wf (c : GClaim) : Bool :=
  decide c.p.Prime && c.prog.all (fun op => decide (2 ≤ opTarget op)) &&
    c.ms.all (fun m => decide (m.2.1 < c.ts.length)) &&
    (c.wa ++ c.wb).all (fun q =>
      c.ns.any (fun n => decide (n.1 = q.1)) || c.ms.any (fun m => decide (m.1 = q.1)))

@[expose] def GClaim.check {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (c : GClaim) :
    Bool :=
  c.wf && mcertCheck O sA sB ⟨c.nregs, c.prog, c.facts⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
