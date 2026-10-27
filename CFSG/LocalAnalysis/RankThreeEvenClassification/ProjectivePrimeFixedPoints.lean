module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ProjectiveLinearActions

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem linear_pElement_has_nonzero_fixed_vector {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space] [IsAlgClosed field]
    [FiniteDimensional field space] [Nontrivial space]
    (prime : ℕ) (hprime : prime.Prime) [CharP field prime]
    (equivalence : space ≃ₗ[field] space) (exponent : ℕ)
    (hpower : equivalence ^ (prime ^ exponent) = 1) :
    ∃ member : space, member ≠ 0 ∧ equivalence member = member := by
  obtain ⟨eigenvalue, heigenvalue⟩ := Module.End.exists_eigenvalue (equivalence : Module.End field space)
  obtain ⟨member, heigenvector⟩ := heigenvalue.exists_hasEigenvector
  have hmemberNe := (Module.End.hasEigenvector_iff.mp heigenvector).2
  have heq : equivalence member = eigenvalue • member := heigenvector.apply_eq_smul
  have hprojective := (projective_fixed_point_iff_eigenvector equivalence member hmemberNe).mpr ⟨eigenvalue, heq⟩
  exact ⟨member, hmemberNe,
    (linear_pElement_fixed_projective_iff_fixed_vector prime hprime equivalence exponent hpower member hmemberNe).mp hprojective⟩

theorem linear_pElement_plane_fixed_subspace_dimension {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space] [IsAlgClosed field]
    [FiniteDimensional field space] (hdimension : Module.finrank field space = 2)
    (prime : ℕ) (hprime : prime.Prime) [CharP field prime]
    (equivalence : space ≃ₗ[field] space) (hne : equivalence ≠ 1) (exponent : ℕ)
    (hpower : equivalence ^ (prime ^ exponent) = 1) :
    Module.finrank field (equivalence : Module.End field space).fixedSubmodule = 1 := by
  have : Nontrivial space := Module.finrank_pos_iff.mp (hdimension ▸ (by omega : 0 < 2))
  obtain ⟨member, hmemberNe, hfixed⟩ :=
    linear_pElement_has_nonzero_fixed_vector prime hprime equivalence exponent hpower
  let fixed := (equivalence : Module.End field space).fixedSubmodule
  have hfixedNe : fixed ≠ ⊥ := by
    apply (Submodule.ne_bot_iff fixed).mpr
    exact ⟨member, LinearMap.mem_fixedSubmodule_iff.mpr hfixed, hmemberNe⟩
  have hfixedProper : fixed ≠ ⊤ := by
    intro heq
    have hlinear := LinearMap.fixedSubmodule_eq_top_iff.mp heq
    apply hne
    apply LinearEquiv.ext
    intro element
    exact DFunLike.congr_fun hlinear element
  have hupper := Submodule.finrank_lt hfixedProper
  have hlower : Module.finrank field fixed ≠ 0 := fun heq => hfixedNe (Submodule.finrank_eq_zero.mp heq)
  rw [hdimension] at hupper
  change Module.finrank field fixed = 1
  omega

theorem linear_pElement_plane_fixed_points_unique {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space] [IsAlgClosed field]
    [FiniteDimensional field space] (hdimension : Module.finrank field space = 2)
    (prime : ℕ) (hprime : prime.Prime) [CharP field prime]
    (equivalence : space ≃ₗ[field] space) (hne : equivalence ≠ 1) (exponent : ℕ)
    (hpower : equivalence ^ (prime ^ exponent) = 1)
    (first second : Projectivization field space)
    (hfirst : linearProjectiveAction field space equivalence first = first)
    (hsecond : linearProjectiveAction field space equivalence second = second) : first = second := by
  let fixed := (equivalence : Module.End field space).fixedSubmodule
  have hfixedDimension := linear_pElement_plane_fixed_subspace_dimension hdimension prime hprime equivalence hne exponent hpower
  have hfirstFixed : equivalence first.rep = first.rep := by
    apply (linear_pElement_fixed_projective_iff_fixed_vector prime hprime equivalence exponent hpower first.rep first.rep_nonzero).mp
    simpa only [Projectivization.mk_rep] using hfirst
  have hsecondFixed : equivalence second.rep = second.rep := by
    apply (linear_pElement_fixed_projective_iff_fixed_vector prime hprime equivalence exponent hpower second.rep second.rep_nonzero).mp
    simpa only [Projectivization.mk_rep] using hsecond
  let firstVector : fixed := ⟨first.rep, LinearMap.mem_fixedSubmodule_iff.mpr hfirstFixed⟩
  let secondVector : fixed := ⟨second.rep, LinearMap.mem_fixedSubmodule_iff.mpr hsecondFixed⟩
  have hfirstNe : firstVector ≠ 0 := fun heq => first.rep_nonzero (congrArg Subtype.val heq)
  obtain ⟨scalar, hscalar⟩ := (finrank_eq_one_iff_of_nonzero' firstVector hfirstNe).mp hfixedDimension secondVector
  have hambient : scalar • first.rep = second.rep := congrArg (fun value : fixed => (value : space)) hscalar
  have hprojective : Projectivization.mk field second.rep second.rep_nonzero =
      Projectivization.mk field first.rep first.rep_nonzero :=
    (Projectivization.mk_eq_mk_iff' field _ _ _ _).mpr ⟨scalar, hambient⟩
  simpa only [Projectivization.mk_rep] using hprojective.symm

theorem linear_pElement_plane_has_unique_projective_fixed_point {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space] [IsAlgClosed field]
    [FiniteDimensional field space] (hdimension : Module.finrank field space = 2)
    (prime : ℕ) (hprime : prime.Prime) [CharP field prime]
    (equivalence : space ≃ₗ[field] space) (hne : equivalence ≠ 1) (exponent : ℕ)
    (hpower : equivalence ^ (prime ^ exponent) = 1) :
    ∃! point : Projectivization field space, linearProjectiveAction field space equivalence point = point := by
  have : Nontrivial space := Module.finrank_pos_iff.mp (hdimension ▸ (by omega : 0 < 2))
  obtain ⟨member, hmemberNe, hfixed⟩ :=
    linear_pElement_has_nonzero_fixed_vector prime hprime equivalence exponent hpower
  let point := Projectivization.mk field member hmemberNe
  have hpoint : linearProjectiveAction field space equivalence point = point :=
    (linear_pElement_fixed_projective_iff_fixed_vector prime hprime equivalence exponent hpower member hmemberNe).mpr hfixed
  exact ⟨point, hpoint, fun other hother =>
    linear_pElement_plane_fixed_points_unique hdimension prime hprime equivalence hne exponent hpower other point hother hpoint⟩

end CFSG.RankThreeEvenClassification.Helpers
