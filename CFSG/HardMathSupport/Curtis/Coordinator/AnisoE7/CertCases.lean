module

public import CFSG.RankThree.PartOne.KE.E7ThreeLatticeInputs

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.Blueprint CFSG.Blueprint.Chevalley

@[expose] def sigma0 : List ℤ := [0, 0, 0, 0, 0, 0, -1]

@[expose] def negWList : List (List ℤ) := lsmul Tag.E7.rank (-1) e7T3WList

@[expose] def negWorbit (j : ℕ) : List ℤ := (fun v => lmulVec Tag.E7.rank negWList v)^[j] sigma0

theorem cert_cases : ∀ c ∈ e7T3Certs, sigma0 ∈ c.rootList →
    (c.comps.map E7T3Comp.kind = [1] ∧ ∀ l ∈ c.rootList, ∃ j < 6, l = negWorbit j) ∨
      c.comps.map E7T3Comp.kind = [3] ∨ c.comps.map E7T3Comp.kind = [0, 1] := by
  decide +kernel

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
