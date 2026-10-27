module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankOneSchreier
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankTwoSchreier

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem unitary_classical_model_schreier {H : Type} [Group H] {n p f : ℕ}
    (hH : StatedClassicalModel H .PSU n p f) :
    derivedSeries (Outer H) 2 = ⊥ ∧ Group.IsSolvable (Outer H) := by
  have hn : 3 ≤ n := by
    obtain ⟨⟨-, -, hn, -⟩, -⟩ := hH
    exact hn
  rcases (by omega : n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n) with rfl | hn' | hn' | hn'
  · exact unitary_rank_one_classical_model_schreier hH
  · exact unitary_rank_two_classical_model_schreier (Or.inl hn') hH
  · exact unitary_rank_two_classical_model_schreier (Or.inr hn') hH
  · exact unitary_higher_classical_model_schreier hn' hH

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
