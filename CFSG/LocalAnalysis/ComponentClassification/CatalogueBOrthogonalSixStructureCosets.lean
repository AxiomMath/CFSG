module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixExhaustion

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSix

open Matrix CatalogueBOrthogonalFourNonsplit

universe u

variable {K : Type u} [Field K]

theorem sixGamma_inv (delta : K) : (sixGamma delta)⁻¹ = sixGamma delta := by
  apply inv_eq_of_mul_eq_one_left
  exact sixGamma_square delta

theorem six_gamma_kappa (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0)
    (g : sixSimilitudes delta) :
    sixGamma delta * kappa delta h2 g =
      kappa delta h2 (sixConjugateD delta g) * sixGamma delta := by
  have hh := congrArg (fun z : SixIsometries delta => z * sixGamma delta)
    (sixGamma_kappa_gamma delta h2 g)
  simpa only [mul_assoc, sixGamma_square, mul_one] using hh

@[expose] def sixCosets (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0) :
    Subgroup (SixIsometries delta) where
  carrier := {z | ∃ g : sixSimilitudes delta,
    z = kappa delta h2 g ∨ z = kappa delta h2 g * sixGamma delta}
  one_mem' := ⟨1, Or.inl (map_one _).symm⟩
  mul_mem' := by
    rintro a b ⟨g, rfl | rfl⟩ ⟨h, rfl | rfl⟩
    · exact ⟨g * h, Or.inl (map_mul _ _ _).symm⟩
    · exact ⟨g * h, Or.inr (by rw [map_mul, mul_assoc])⟩
    · refine ⟨g * sixConjugateD delta h, Or.inr ?_⟩
      rw [map_mul, mul_assoc, six_gamma_kappa, ← mul_assoc]
    · refine ⟨g * sixConjugateD delta h, Or.inl ?_⟩
      rw [map_mul, mul_assoc, ← mul_assoc (sixGamma delta), six_gamma_kappa,
        mul_assoc, sixGamma_square, mul_one]
  inv_mem' := by
    rintro a ⟨g, rfl | rfl⟩
    · exact ⟨g⁻¹, Or.inl (map_inv _ _).symm⟩
    · refine ⟨sixConjugateD delta g⁻¹, Or.inr ?_⟩
      rw [_root_.mul_inv_rev, sixGamma_inv, ← map_inv, six_gamma_kappa]

theorem sixCosets_eq_top (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0) :
    sixCosets delta h2 = ⊤ := by
  have hh : sixGenerated delta h2 ≤ sixCosets delta h2 := by
    apply sup_le
    · rintro a ⟨g, rfl⟩
      exact ⟨g, Or.inl rfl⟩
    · apply (Subgroup.closure_le _).mpr
      rintro a (rfl : a = sixGamma delta)
      exact ⟨1, Or.inr (by rw [map_one, one_mul])⟩
  rw [sixGenerated_eq_top delta h2] at hh
  exact top_le_iff.mp hh

theorem six_full_isometry_exhaustion (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (z : SixIsometries delta) :
    ∃ g : sixSimilitudes delta,
      z = kappa delta h2 g ∨ z = kappa delta h2 g * sixGamma delta := by
  change z ∈ sixCosets delta h2
  rw [sixCosets_eq_top]
  exact Subgroup.mem_top _

theorem six_kappa_range_index_dvd_two (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) : (kappa delta h2).range.index ∣ 2 := by
  apply Subgroup.index_dvd_two_iff.mpr
  refine ⟨sixGamma delta, fun z => ?_⟩
  obtain ⟨g, rfl | rfl⟩ := six_full_isometry_exhaustion delta h2 z
  · exact Or.inr ⟨g, rfl⟩
  · exact Or.inl (by simpa only [mul_assoc, sixGamma_square, mul_one] using
      (show kappa delta h2 g ∈ (kappa delta h2).range from ⟨g, rfl⟩))

theorem six_kappa_range_index_le_two (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) : (kappa delta h2).range.index ≤ 2 :=
  Nat.le_of_dvd (by decide) (six_kappa_range_index_dvd_two delta h2)

instance sixKappaRangeNormal (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0) :
    (kappa delta h2).range.Normal := by
  obtain hh | hh := Nat.prime_two.eq_one_or_self_of_dvd _
    (six_kappa_range_index_dvd_two delta h2)
  · exact Subgroup.normal_of_index_eq_one hh
  · exact Subgroup.normal_of_index_eq_two hh

end CFSG.ComponentClassification.CatalogueBOrthogonalSix
