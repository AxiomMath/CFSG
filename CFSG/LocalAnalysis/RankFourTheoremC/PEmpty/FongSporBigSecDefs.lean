module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMSecDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.RankThree.Asc83Table.Native CFSG.SectionRank.Native

structure SClaim where
  nregs : ℕ
  prog : List Op
  p : ℕ
  rz : ℕ
  zt : ℕ
  rt : ℕ
  tt : ℕ
  rg1 : ℕ
  rg2 : ℕ
  sreg : List ℕ
  sord : List ℕ
  simple : PSimple
  tg : ℕ
  t3 : ℕ

namespace SClaim

@[expose] def sr (c : SClaim) (k : ℕ) : ℕ := c.sreg.getD k 0

@[expose] def gReg (c : SClaim) (j : Bool) : ℕ := if j then c.rg2 else c.rg1

@[expose] def kFacts (c : SClaim) (k : ℕ) : List MFact :=
  [.ord (c.sr k) (c.sord.getD k 1)] ++
  (if k = 0 then [.eq [(c.sr k, 1)] []]
   else [.eq [(c.sr k, 1)]
      [(c.sr (c.simple.par.getD k 0), 1), (c.gReg (c.simple.gen.getD k false), 1)]]) ++
  [.eq [(c.sr k, 1), (c.rg1, 1)] [(c.sr (c.simple.suc1.getD k 0), 1)],
   .eq [(c.sr k, 1), (c.rg2, 1)] [(c.sr (c.simple.suc2.getD k 0), 1)]] ++
  (match c.simple.cls.getD k none with
    | none => [.eq [(c.sr k, 1)] []]
    | some (u, i) =>
      [.eq [(c.sr k, 1), (c.sr u, 1)] [(c.sr u, 1), (c.sr (c.simple.reps.getD i 0), 1)]])

@[expose] def repFacts (c : SClaim) (i : ℕ) : List MFact :=
  [.eq [(c.rg1, 1)] ((c.simple.nc.getD i ([], [])).1.map fun l => (c.sr l, 1)),
   .eq [(c.rg2, 1)] ((c.simple.nc.getD i ([], [])).2.map fun l => (c.sr l, 1))]

@[expose] def facts (c : SClaim) : List MFact :=
  [.ord c.rz c.p, .ne [(c.rz, 1)] [] c.zt, .ord c.rt 2, .ne [(c.rt, 1)] [] c.tt,
    .eq [(c.rz, 1), (c.rt, 1)] [(c.rt, 1), (c.rz, 1)],
    .eq [(c.rg1, 1), (c.rt, 1)] [(c.rt, 1), (c.rg1, 1)],
    .eq [(c.rg2, 1), (c.rt, 1)] [(c.rt, 1), (c.rg2, 1)],
    .ord c.rg1 c.simple.o1, .ord c.rg2 c.simple.o2] ++
  (List.range c.simple.par.length).flatMap c.kFacts ++
  (List.range c.simple.reps.length).flatMap c.repFacts ++
  [.ne [(c.rg1, 1), (c.rg2, 1)] [(c.rg2, 1), (c.rg1, 1)] c.tg,
    .eq [(c.sr c.simple.k3, 3)] [], .ne [(c.sr c.simple.k3, 1)] [] c.t3,
    .eq [(c.sr c.simple.kz, 1)] [(c.rz, 1)]]

@[expose] def wf (c : SClaim) : Bool := decide c.p.Prime && c.simple.wfB

@[expose] def check {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (c : SClaim) : Bool :=
  c.wf && mcertCheck O sA sB ⟨c.nregs, c.prog, c.facts⟩

end SClaim

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
