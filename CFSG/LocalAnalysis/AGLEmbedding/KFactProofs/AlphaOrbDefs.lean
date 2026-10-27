module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordDefs

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

@[expose] def matVecL (p n : Nat) (M c : List Nat) : List Nat :=
  (List.range n).map fun k =>
    ((List.range n).foldl (fun s i => s + M.getD (n * k + i) 0 * c.getD i 0) 0) % p

@[expose] def NMod.orbChk (p : Nat) (m : NMod) (target : List (List Nat)) :
    List (List Nat) → List (Nat × Nat) → Bool
  | known, [] => target.all fun c => known.contains c
  | known, (j, par) :: rest =>
    decide (j < m.acts.length) && decide (par < known.length) &&
      m.orbChk p target (known ++ [matVecL p m.basis.length (m.acts.getD j default).mat
        (known.getD par [])]) rest

@[expose] def NMod.wfO (p : Nat) (m : NMod) (orb : List (Nat × Nat)) : Bool :=
  decide (2 ≤ p) &&
  m.acts.all (fun g => decide (g.mat.length = m.basis.length * m.basis.length)) &&
  m.orbChk p ((allVecs p m.basis.length).filter fun c => !c.all (· == 0)) (m.indep.map (·.1)) orb

@[expose] def modCheckV {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (nregs : Nat)
    (prog : List Op) (p : Nat) (m : NMod) (tops : List Pc) (tidx : List Nat) (s : Nat)
    (orb : List (Nat × Nat)) (cf : Nat → Nat → Nat → Int)
    (ci : Nat → Nat → Nat → Nat → Nat → Int) (ct : Nat → Nat → Nat → Nat → Int) : Bool :=
  mcertCheck O sA sB ⟨nregs, prog, m.modFactsW p tops⟩ && m.wfO p orb &&
  pcWf (tops ++ m.basisPc p) && tops.all (fun q => m.acts.any (·.reg == q.reg)) &&
  m.wOK p tops tidx s && decide (p ≤ m.basis.length) && m.funOK p cf && m.altOK p ci ct tgtAlt

end CFSG.AGLEmbedding.R3
