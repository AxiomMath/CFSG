module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructureCosets

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSix

open Matrix CatalogueBOrthogonalFourNonsplit

universe u

variable {K : Type u} [Field K]

@[expose] def sixSpecialImage (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0) :
    Subgroup (SixIsometries delta) := (sixSpecialKappa delta h2).range

theorem sixSpecialImage_le_kappaRange (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) : sixSpecialImage delta h2 ≤ (kappa delta h2).range := by
  rintro z ⟨g, rfl⟩
  exact ⟨sixSpecialInclusion delta g, rfl⟩

theorem sixSpecial_multiplier (delta : K) (g : sixSpecialUnitary delta) :
    sixMultiplier delta (sixSpecialInclusion delta g) = 1 := by
  apply (sixMultiplier delta).mem_ker.mp
  exact (sixMultiplier_kernel_iff delta _).mpr g.property

theorem six_kappa_mem_specialImage_of_multiplier (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (g : sixSimilitudes delta) (hg : sixMultiplier delta g = 1) :
    kappa delta h2 g ∈ sixSpecialImage delta h2 := by
  have hi : g ∈ (sixSpecialInclusion delta).range := by
    rw [sixSpecialInclusion_range]
    exact (sixMultiplier delta).mem_ker.mpr hg
  obtain ⟨u, rfl⟩ := hi
  exact ⟨u, rfl⟩

theorem six_kappa_conjugation_mem_specialImage (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (g : sixSimilitudes delta) {z : SixIsometries delta}
    (hz : z ∈ sixSpecialImage delta h2) :
    kappa delta h2 g * z * (kappa delta h2 g)⁻¹ ∈ sixSpecialImage delta h2 := by
  obtain ⟨u, rfl⟩ := hz
  change kappa delta h2 g * kappa delta h2 (sixSpecialInclusion delta u) *
    (kappa delta h2 g)⁻¹ ∈ sixSpecialImage delta h2
  rw [← map_inv, ← map_mul, ← map_mul]
  apply six_kappa_mem_specialImage_of_multiplier
  rw [map_mul, map_mul, map_inv, sixSpecial_multiplier, mul_one, mul_inv_cancel]

theorem six_gamma_conjugation_mem_specialImage (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) {z : SixIsometries delta} (hz : z ∈ sixSpecialImage delta h2) :
    sixGamma delta * z * sixGamma delta ∈ sixSpecialImage delta h2 := by
  obtain ⟨u, rfl⟩ := hz
  change sixGamma delta * kappa delta h2 (sixSpecialInclusion delta u) *
    sixGamma delta ∈ sixSpecialImage delta h2
  rw [sixGamma_kappa_gamma]
  apply six_kappa_mem_specialImage_of_multiplier
  rw [sixMultiplier_conjugate, sixSpecial_multiplier]

instance sixSpecialImageNormal (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0) :
    (sixSpecialImage delta h2).Normal where
  conj_mem z hz g := by
    obtain ⟨d, rfl | rfl⟩ := six_full_isometry_exhaustion delta h2 g
    · exact six_kappa_conjugation_mem_specialImage delta h2 d hz
    · simpa only [_root_.mul_inv_rev, sixGamma_inv, mul_assoc] using
        six_kappa_conjugation_mem_specialImage delta h2 d
          (six_gamma_conjugation_mem_specialImage delta h2 hz)

end CFSG.ComponentClassification.CatalogueBOrthogonalSix
