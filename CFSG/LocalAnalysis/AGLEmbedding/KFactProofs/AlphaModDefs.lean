module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.RankThreeDefs

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

structure NTest where
  vec : List Nat
  t : Nat
deriving Inhabited

@[expose] def NMod.basisPc (p : Nat) (m : NMod) : List Pc :=
  (List.range m.basis.length).map fun k =>
    { reg := m.basis.getD k 0, ord := p, pw := [],
      cj := ((List.range m.basis.length).filter (k < ·)).map fun l =>
        (m.basis.getD l 0, [(m.basis.getD l 0, 1)]) }

@[expose] def NMod.testFacts (m : NMod) : List Pc → List NTest → List MFact
  | q :: qs, T :: ts =>
    (qs.map fun r => MFact.eq (m.word T.vec ++ [(r.reg, 1)]) ([(r.reg, 1)] ++ m.word T.vec)) ++
    [MFact.ne (m.word T.vec ++ [(q.reg, 1)]) ([(q.reg, 1)] ++ m.word T.vec) T.t] ++
    m.testFacts qs ts
  | _, _ => []

@[expose] def NMod.modFacts (p : Nat) (m : NMod) (tops : List Pc) (tests : List NTest) :
    List MFact :=
  m.facts p ++ (tops ++ m.basisPc p).flatMap (Pc.facts p) ++ m.testFacts tops tests

@[expose] def modCheck {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (nregs : Nat)
    (prog : List Op) (p : Nat) (m : NMod) (tops : List Pc) (tests : List NTest)
    (cf : Nat → Nat → Nat → Int) (ci : Nat → Nat → Nat → Nat → Nat → Int)
    (ct : Nat → Nat → Nat → Nat → Int) : Bool :=
  mcertCheck O sA sB ⟨nregs, prog, m.modFacts p tops tests⟩ && m.wf p &&
  pcWf (tops ++ m.basisPc p) && decide (tests.length = tops.length) &&
  tops.all (fun q => m.acts.any (·.reg == q.reg)) && decide (p ≤ m.basis.length) &&
  m.funOK p cf && m.altOK p ci ct tgtAlt

end CFSG.AGLEmbedding.R3
