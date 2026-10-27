module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMGenDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalSimpleDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.RankThree.Asc83Table.Native CFSG.SectionRank.Native

namespace PSimple

@[expose] def wfB (c : PSimple) : Bool :=
  let n := c.par.length
  decide (0 < n) && decide (c.gen.length = n) && decide (c.suc1.length = n) &&
  decide (c.suc2.length = n) && decide (c.cls.length = n) && decide (0 < c.o1) &&
  decide (0 < c.o2) &&
  (List.range n).all (fun k =>
    decide (k = 0 ∨ c.par.getD k 0 < k) &&
    decide (c.suc1.getD k 0 < n) && decide (c.suc2.getD k 0 < n) &&
    (match c.cls.getD k none with
      | none => true
      | some (u, i) => decide (u < n) && decide (i < c.reps.length))) &&
  c.reps.all (fun r => decide (r < n)) &&
  (List.range c.reps.length).all (fun i =>
    (c.nc.getD i ([], [])).1.all (fun l => decide (l < n) &&
      decide ((c.cls.getD l none).map Prod.snd = some i)) &&
    (c.nc.getD i ([], [])).2.all (fun l => decide (l < n) &&
      decide ((c.cls.getD l none).map Prod.snd = some i))) &&
  decide (c.k3 < n) && decide (c.kz < n)

end PSimple

structure MSec where
  base : MGen
  nregs : ℕ
  prog : List Op
  rg1 : ℕ
  rg2 : ℕ
  h1 : List (ℕ × ℕ)
  h2 : List (ℕ × ℕ)
  sreg : List ℕ
  sord : List ℕ
  simple : PSimple
  tg : ℕ
  t3 : ℕ

namespace MSec

@[expose] def gReg (c : MSec) (j : Bool) : ℕ := if j then c.rg2 else c.rg1

@[expose] def sr (c : MSec) (k : ℕ) : ℕ := c.sreg.getD k 0

@[expose] def kFacts (c : MSec) (k : ℕ) : List MFact :=
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

@[expose] def repFacts (c : MSec) (i : ℕ) : List MFact :=
  [.eq [(c.rg1, 1)] ((c.simple.nc.getD i ([], [])).1.map fun l => (c.sr l, 1)),
   .eq [(c.rg2, 1)] ((c.simple.nc.getD i ([], [])).2.map fun l => (c.sr l, 1))]

@[expose] def simpleFacts (c : MSec) : List MFact :=
  [.ord c.rg1 c.simple.o1, .ord c.rg2 c.simple.o2,
    .eq [(c.rg1, 1)] (c.base.g.idxWord c.h1), .eq [(c.rg2, 1)] (c.base.g.idxWord c.h2)] ++
  (List.range c.simple.par.length).flatMap c.kFacts ++
  (List.range c.simple.reps.length).flatMap c.repFacts ++
  [.ne [(c.rg1, 1), (c.rg2, 1)] [(c.rg2, 1), (c.rg1, 1)] c.tg,
   .eq [(c.sr c.simple.k3, 3)] [], .ne [(c.sr c.simple.k3, 1)] [] c.t3,
   .eq [(c.sr c.simple.kz, 1)] (pwToWord c.base.g.z)]

@[expose] def facts (c : MSec) : List MFact := c.base.baseFacts ++ c.simpleFacts

@[expose] def wf (c : MSec) : Bool :=
  decide c.base.g.p.Prime && decide (c.base.tts.length = c.base.g.ts.length) &&
  c.base.g.ms.all (fun m => decide (m.2 < c.base.g.ts.length)) &&
  c.h1.all (fun q => decide (q.1 < c.base.g.ns.length + c.base.g.ms.length)) &&
  c.h2.all (fun q => decide (q.1 < c.base.g.ns.length + c.base.g.ms.length)) &&
  c.simple.wfB

@[expose] def check {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (c : MSec) : Bool :=
  c.wf && mcertCheck O sA sB ⟨c.nregs, c.prog, c.facts⟩

end MSec

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
