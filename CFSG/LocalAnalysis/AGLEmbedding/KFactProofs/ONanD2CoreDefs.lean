module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRankDefs

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

@[expose] def coreGenCheck {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String)
    (nregs : Nat) (prog : List Op) (D : RSpec) : Bool :=
  let R := O.regsOf sA sB nregs prog
  (decide (2 ≤ nregs) && prog.all (Op.lt nregs) && D.facts.all (factOK O R nregs)) &&
  decide (D.rA < nregs) && decide (D.rB < nregs) &&
  O.eq R[D.rA]! (O.decode sA) && O.eq R[D.rB]! (O.decode sB) && D.wf

end CFSG.AGLEmbedding.R3
