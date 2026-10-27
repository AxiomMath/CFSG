module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRealization
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearQuotient
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherOuterNormalizer

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem derivedSeries_two_eq_bot_of_eq_semilinearPointGroup (h : UnitaryFieldData p f K)
    {H : Subgroup (Equiv.Perm (hypIsotropicLines h r ε))} (hH : H = semilinearPointGroup h r ε)
    [((hypProjLineAction h r ε).range.subgroupOf H).Normal] :
    derivedSeries (H ⧸ (hypProjLineAction h r ε).range.subgroupOf H) 2 = ⊥ := by
  subst hH
  exact (unitary_semilinear_point_quotient h r ε).2.1

theorem unitary_higher_permutation_normalizer (h : UnitaryFieldData p f K) (hr : 3 ≤ r)
    (hε : ε ≤ 1) :
    lineNormalizer h r ε = semilinearPointGroup h r ε ∧
    derivedSeries (lineNormalizer h r ε ⧸
      (hypProjLineAction h r ε).range.subgroupOf (lineNormalizer h r ε)) 2 = ⊥ := by
  have hEq : lineNormalizer h r ε = semilinearPointGroup h r ε := by
    refine le_antisymm (fun φ hφ => ?_) semilinearPointGroup_le_normalizer
    obtain ⟨x, rfl⟩ := (unitary_higher_geometric_semilinear_realization h hr hε).1 φ
      ((unitary_normalizer_preserves_orthogonality.{0} h (by omega)).1 φ hφ)
    exact ⟨x, rfl⟩
  exact ⟨hEq, derivedSeries_two_eq_bot_of_eq_semilinearPointGroup h hEq⟩

theorem unitary_higher_classical_model_schreier {H : Type} [Group H] {n p f : ℕ} (hn : 6 ≤ n)
    (hH : StatedClassicalModel H .PSU n p f) :
    derivedSeries (Outer H) 2 = ⊥ ∧ Group.IsSolvable (Outer H) := by
  obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε, ε ≤ 1 ∧ n = 2 * r + ε := ⟨n / 2, n % 2, by omega, by omega⟩
  have hr : 3 ≤ r := by omega
  obtain ⟨⟨K, _, h, ⟨e⟩⟩, hall⟩ := unitary_classical_model_outer_normalizer hH
  obtain ⟨-, ⟨E⟩, -⟩ := hall K h e
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) h
  obtain ⟨j, hj⟩ := exists_transportLines h hR
  obtain ⟨E₂⟩ := nonempty_normalizerQuotient_mulEquiv j (hypProjTransport h hR) hj
  have hder := (unitary_higher_permutation_normalizer h hr hε).2
  have F := E.trans E₂.symm
  have h2 : derivedSeries (Outer H) 2 = ⊥ := by
    rw [← map_derivedSeries_eq (f := F.symm.toMonoidHom) F.symm.surjective, hder,
      Subgroup.map_bot]
  exact ⟨h2, (Group.isSolvable_def _).mpr ⟨2, h2⟩⟩

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
