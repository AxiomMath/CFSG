module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankOneNormalizer

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem unitary_rank_one_classical_model_schreier {H : Type} [Group H] {p f : ℕ}
    (hH : StatedClassicalModel H .PSU 3 p f) :
    derivedSeries (Outer H) 2 = ⊥ ∧ Group.IsSolvable (Outer H) := by
  have hq : 2 < p ^ f := by
    obtain ⟨⟨hp, hf, -, hne⟩, -⟩ := hH
    have h2 : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    have h3 : p ^ f ≠ 2 := fun h0 => hne (by rw [h0])
    omega
  have hH' : StatedClassicalModel H .PSU (2 * 1 + 1) p f := hH
  obtain ⟨⟨K, _, h, ⟨e⟩⟩, hall⟩ := unitary_classical_model_outer_normalizer hH'
  obtain ⟨-, ⟨E⟩, -⟩ := hall K h e
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) h
  obtain ⟨j, hj⟩ := exists_transportLines h hR
  obtain ⟨E₂⟩ := nonempty_normalizerQuotient_mulEquiv j (hypProjTransport h hR) hj
  have hder := (unitary_rank_one_permutation_normalizer h hq).2
  have F := E.trans E₂.symm
  have h2 : derivedSeries (Outer H) 2 = ⊥ := by
    rw [← map_derivedSeries_eq (f := F.symm.toMonoidHom) F.symm.surjective]
    exact (congrArg (Subgroup.map F.symm.toMonoidHom) hder).trans (Subgroup.map_bot _)
  exact ⟨h2, (Group.isSolvable_def _).mpr ⟨2, h2⟩⟩

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
