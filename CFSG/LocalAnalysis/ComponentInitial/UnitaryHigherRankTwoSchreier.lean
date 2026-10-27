module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankTwoRigidity
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSchreier
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankTwoOpposite

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {p f : ℕ} {K : Type} [Field K] {ε : ℕ}

theorem unitary_rank_two_permutation_normalizer (h : UnitaryFieldData p f K) (hε : ε ≤ 1) :
    lineNormalizer h 2 ε = semilinearPointGroup h 2 ε ∧
    derivedSeries (lineNormalizer h 2 ε ⧸
      (hypProjLineAction h 2 ε).range.subgroupOf (lineNormalizer h 2 ε)) 2 = ⊥ := by
  have hEq : lineNormalizer h 2 ε = semilinearPointGroup h 2 ε := by
    refine le_antisymm (fun φ hφ => ?_) semilinearPointGroup_le_normalizer
    have hE : ∀ x : semilinearSimilitudes h 2 ε,
        semilinearPointAction h 2 ε x ∈ lineNormalizer h 2 ε := fun x =>
      semilinearPointGroup_le_normalizer ⟨x, rfl⟩
    obtain ⟨x₁, -, hx₁⟩ := unitary_rank_two_opposite_normalization h hε φ hφ
    obtain ⟨φ₁, hφ₁def⟩ : ∃ φ₁ : Equiv.Perm (hypIsotropicLines h 2 ε),
        φ₁ = (semilinearPointAction h 2 ε x₁)⁻¹ * φ := ⟨_, rfl⟩
    have hφ₁N : φ₁ ∈ lineNormalizer h 2 ε := by
      rw [hφ₁def]
      exact mul_mem (inv_mem (hE x₁)) hφ
    have hfix₁ : ∀ L : hypIsotropicLines h 2 ε,
        ((L : Submodule K (HypIndex 2 ε → K)) ≤ hypX K 2 ε ∨
          (L : Submodule K (HypIndex 2 ε → K)) ≤ hypY K 2 ε) → φ₁ L = L := fun L hL => by
      rw [hφ₁def, Equiv.Perm.mul_apply, hx₁ L hL, Equiv.Perm.inv_eq_iff_eq]
    obtain ⟨c, d, hc, hd, -, -, hD, hDL⟩ := unitary_rank_two_hyperbolic_rigidity h hε φ₁ hφ₁N
      (fun L hL => hfix₁ L (Or.inl hL)) (fun L hL => hfix₁ L (Or.inr hL))
    set x₂ : semilinearSimilitudes h 2 ε := ⟨_, hD⟩ with hx₂
    obtain ⟨φ₂, hφ₂def⟩ : ∃ φ₂ : Equiv.Perm (hypIsotropicLines h 2 ε),
        φ₂ = (semilinearPointAction h 2 ε x₂)⁻¹ * φ₁ := ⟨_, rfl⟩
    have hφ₂N : φ₂ ∈ lineNormalizer h 2 ε := by
      rw [hφ₂def]
      exact mul_mem (inv_mem (hE x₂)) hφ₁N
    have hφ₂ := (unitary_normalizer_preserves_orthogonality.{0} h (le_refl 2)).1 φ₂ hφ₂N
    have hfix₂ : ∀ L : hypIsotropicLines h 2 ε,
        (L : Submodule K (HypIndex 2 ε → K)) ≤ hypH K 2 ε → φ₂ L = L := fun L hL => by
      rw [hφ₂def, Equiv.Perm.mul_apply, hDL L hL, Equiv.Perm.inv_eq_iff_eq]
    obtain ⟨x₃, hx₃⟩ := realize_of_fix_hypH h (le_refl 2) hε hφ₂ hfix₂
    refine ⟨x₁ * x₂ * x₃, ?_⟩
    rw [map_mul, map_mul, ← hx₃, hφ₂def, hφ₁def]
    group
  exact ⟨hEq, derivedSeries_two_eq_bot_of_eq_semilinearPointGroup h hEq⟩

theorem unitary_rank_two_classical_model_schreier {H : Type} [Group H] {n p f : ℕ}
    (hn : n = 4 ∨ n = 5) (hH : StatedClassicalModel H .PSU n p f) :
    derivedSeries (Outer H) 2 = ⊥ ∧ Group.IsSolvable (Outer H) := by
  obtain ⟨ε, hε, rfl⟩ : ∃ ε, ε ≤ 1 ∧ n = 2 * 2 + ε := ⟨n - 4, by omega, by omega⟩
  obtain ⟨⟨K, _, h, ⟨e⟩⟩, hall⟩ := unitary_classical_model_outer_normalizer hH
  obtain ⟨-, ⟨E⟩, -⟩ := hall K h e
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := ε) h
  obtain ⟨j, hj⟩ := exists_transportLines h hR
  obtain ⟨E₂⟩ := nonempty_normalizerQuotient_mulEquiv j (hypProjTransport h hR) hj
  have hder := (unitary_rank_two_permutation_normalizer h hε).2
  have F := E.trans E₂.symm
  have h2 : derivedSeries (Outer H) 2 = ⊥ := by
    rw [← map_derivedSeries_eq (f := F.symm.toMonoidHom) F.symm.surjective, hder,
      Subgroup.map_bot]
  exact ⟨h2, (Group.isSolvable_def _).mpr ⟨2, h2⟩⟩

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
