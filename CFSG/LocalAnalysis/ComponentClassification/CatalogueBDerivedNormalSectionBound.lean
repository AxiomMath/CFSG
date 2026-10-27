module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionAction

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBDerivedNormalSection

universe u

variable {E : Type u} [Group E]

theorem theta_derivedSeries_map_bot (N Z : Subgroup E) [N.Normal] [Z.Normal] (r : ℕ)
    (hquotient : derivedSeries (E ⧸ N) r = ⊥) :
    (derivedSeries E (r + 1)).map (theta N Z) = ⊥ := by
  apply (Subgroup.map_eq_bot_iff _).mpr
  exact (derivedSeries_succ_le_derivedNormalSubgroup N r hquotient).trans
    (derivedNormalSubgroup_le_theta_kernel N Z)

theorem theta_image_derivedSeries_bot (N Z : Subgroup E) [N.Normal] [Z.Normal] (r : ℕ)
    (hquotient : derivedSeries (E ⧸ N) r = ⊥) :
    derivedSeries (theta N Z).range (r + 1) = ⊥ := by
  apply Subgroup.map_subtype_inj.mp
  rw [Subgroup.map_bot, ← derivedSeries_range_transport (theta N Z) (r + 1)]
  exact theta_derivedSeries_map_bot N Z r hquotient

theorem derived_normal_section_outer_bound (N Z : Subgroup E) [N.Normal] [Z.Normal]
    (hZ : Z ≤ derivedNormalSubgroup N) (r : ℕ)
    (hquotient : derivedSeries (E ⧸ N) r = ⊥) :
    (sectionDenominator N Z).map (derivedNormalSubgroup N).subtype = Z ∧
      (∀ (e : E) (h : derivedNormalSubgroup N),
        quotientConjugationHom N Z e (sectionProjection N Z h) =
          sectionProjection N Z
            ⟨e * (h : E) * e⁻¹,
              (inferInstance : (derivedNormalSubgroup N).Normal).conj_mem h.val h.property e⟩) ∧
      (∀ h : derivedNormalSubgroup N,
        quotientConjugationHom N Z (h : E) = MulAut.conj (sectionProjection N Z h)) ∧
      derivedNormalSubgroup N ≤ (theta N Z).ker ∧
      derivedSeries (theta N Z).range (r + 1) = ⊥ := by
  refine ⟨sectionDenominator_map N Z hZ, ?_,
    quotientConjugationHom_derivedMember N Z,
    derivedNormalSubgroup_le_theta_kernel N Z,
    theta_image_derivedSeries_bot N Z r hquotient⟩
  exact sectionAutomorphism_mk_literal N Z

end CFSG.ComponentClassification.CatalogueBDerivedNormalSection
