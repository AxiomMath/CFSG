module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModDefs

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

structure NGrp where
  idx : Nat
  w : Word
deriving Inhabited

@[expose] def NMod.grpFacts (m : NMod) (gs : List NGrp) : List MFact :=
  gs.map fun g => MFact.eq [((m.acts.getD g.idx default).reg, 1)] g.w

@[expose] def NMod.modFactsE (p : Nat) (m : NMod) (tops : List Pc) (gs : List NGrp) :
    List MFact :=
  m.facts p ++ (tops ++ m.basisPc p).flatMap (Pc.facts p) ++ m.grpFacts gs

@[expose] def NMod.matDiffer (m : NMod) (a b : Nat) : Bool :=
  (List.range m.basis.length).any fun k => (List.range m.basis.length).any fun l =>
    (m.acts.getD a default).mat.getD (m.basis.length * k + l) 0 !=
      (m.acts.getD b default).mat.getD (m.basis.length * k + l) 0

@[expose] def NMod.grpOK (m : NMod) (tops : List Pc) (gs : List NGrp) : Bool :=
  gs.all (fun g => decide (g.idx < m.acts.length) && g.w.all fun a => tops.any (·.reg == a.1)) &&
  (List.range gs.length).all fun a => (List.range gs.length).all fun b =>
    decide (b ≤ a) || m.matDiffer (gs.getD a default).idx (gs.getD b default).idx

@[expose] def modCheckE {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (nregs : Nat)
    (prog : List Op) (p : Nat) (m : NMod) (tops : List Pc) (gs : List NGrp)
    (cf : Nat → Nat → Nat → Int) (ci : Nat → Nat → Nat → Nat → Nat → Int)
    (ct : Nat → Nat → Nat → Nat → Int) : Bool :=
  mcertCheck O sA sB ⟨nregs, prog, m.modFactsE p tops gs⟩ && m.wf p &&
  pcWf (tops ++ m.basisPc p) && m.acts.all (fun g => g.mat.all (· < p)) &&
  tops.all (fun q => m.acts.any (·.reg == q.reg)) && m.grpOK tops gs &&
  decide (p ≤ m.basis.length) && m.funOK p cf && m.altOK p ci ct tgtAlt

end CFSG.AGLEmbedding.R3
