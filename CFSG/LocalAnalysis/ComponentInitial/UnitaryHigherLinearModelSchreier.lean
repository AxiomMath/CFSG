module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearSchreier
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Assembly.LowTwoRank

theorem linear_higher_classical_model_schreier {S : Type} [Group S] {n p f : ℕ} (hn : 3 ≤ n)
    (hS : StatedClassicalModel S .PSL n p f) :
    derivedSeries (Outer S) 3 = ⊥ ∧ Group.IsSolvable (Outer S) := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := hS
  obtain ⟨⟨E, -⟩, -⟩ := outer_isomorphism ((e.trans
    (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K))
  have hP := (linear_higher_schreier (K := K) hn).1
  have h3 : derivedSeries (Outer S) 3 = ⊥ := by
    rw [← map_derivedSeries_eq (f := E.symm.toMonoidHom) E.symm.surjective]
    exact (congrArg (Subgroup.map E.symm.toMonoidHom) hP).trans (Subgroup.map_bot _)
  exact ⟨h3, (Group.isSolvable_def _).mpr ⟨3, h3⟩⟩

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
