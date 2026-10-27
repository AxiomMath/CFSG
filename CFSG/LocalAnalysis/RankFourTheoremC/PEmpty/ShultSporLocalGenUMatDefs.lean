module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMGenDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.RankThree.Asc83Table.Native CFSG.SectionRank.Native

structure MGenU where
  base : MGen
  us : List PW
  ut : ℕ
  u0 : ℕ
  uz : List (List ℕ × List ℕ)
  ks : List (PW × List (List ℕ × List ℕ))

@[expose] def MGenU.uProd (c : MGenU) (idx : List ℕ) : Word :=
  idx.flatMap fun i => pwToWord (c.us.getD i [])

@[expose] def MGenU.regW (c : MGenU) (i : ℕ) : Word :=
  if i < c.base.g.ns.length + c.base.g.ms.length then c.base.g.regW i
  else pwToWord (c.ks.getD (i - c.base.g.ns.length - c.base.g.ms.length) ([], [])).1

@[expose] def MGenU.idxWord (c : MGenU) (w : List (ℕ × ℕ)) : Word :=
  w.flatMap fun q => mwordPow (c.regW q.1) q.2

@[expose] def MGenU.sqFacts (c : MGenU) : List MFact :=
  c.us.map fun u => MFact.eq (pwToWord u ++ pwToWord u) []

@[expose] def MGenU.commFacts (c : MGenU) : List MFact :=
  c.us.flatMap fun u => c.us.map fun v =>
    MFact.eq (pwToWord u ++ pwToWord v) (pwToWord v ++ pwToWord u)

@[expose] def MGenU.zFacts (c : MGenU) : List MFact :=
  (c.us.zip c.uz).flatMap fun q =>
    [MFact.eq (pwToWord c.base.g.z ++ pwToWord q.1) (c.uProd q.2.1 ++ pwToWord c.base.g.z),
     MFact.eq (pwToWord q.1 ++ pwToWord c.base.g.z) (pwToWord c.base.g.z ++ c.uProd q.2.2)]

@[expose] def MGenU.kFacts (c : MGenU) : List MFact :=
  c.ks.flatMap fun k => (c.us.zip k.2).flatMap fun q =>
    [MFact.eq (pwToWord k.1 ++ pwToWord q.1) (c.uProd q.2.1 ++ pwToWord k.1),
     MFact.eq (pwToWord q.1 ++ pwToWord k.1) (pwToWord k.1 ++ c.uProd q.2.2)]

@[expose] def MGenU.facts (c : MGenU) : List MFact :=
  c.base.baseFacts ++ c.sqFacts ++ c.commFacts ++
    [MFact.ne (pwToWord (c.us.getD 0 [])) [] c.ut] ++ c.zFacts ++ c.kFacts ++
    [MFact.eq [(0, 1)] (c.idxWord c.base.g.wa), MFact.eq [(1, 1)] (c.idxWord c.base.g.wb)]

@[expose] def MGenU.wf (c : MGenU) : Bool :=
  decide (c.base.g.p.Prime ∧ c.base.tts.length = c.base.g.ts.length ∧
    (∀ m ∈ c.base.g.ms, m.2 < c.base.g.ts.length) ∧ c.us ≠ [] ∧
    c.uz.length = c.us.length ∧ (∀ k ∈ c.ks, k.2.length = c.us.length) ∧
    c.u0 < c.base.g.ms.length ∧ (c.base.g.ms.getD c.u0 ([], 0)).1 = c.us.getD 0 [] ∧
    (∀ e ∈ c.uz, (∀ j ∈ e.1, j < c.us.length) ∧ ∀ j ∈ e.2, j < c.us.length) ∧
    (∀ k ∈ c.ks, ∀ e ∈ k.2, (∀ j ∈ e.1, j < c.us.length) ∧ ∀ j ∈ e.2, j < c.us.length) ∧
    (∀ q ∈ c.base.g.wa, q.1 < c.base.g.ns.length + c.base.g.ms.length + c.ks.length) ∧
    ∀ q ∈ c.base.g.wb, q.1 < c.base.g.ns.length + c.base.g.ms.length + c.ks.length)

@[expose] def MGenU.check {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String)
    (c : MGenU) : Bool :=
  c.wf && mcertCheck O sA sB ⟨2, [], c.facts⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
