module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBasic
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBDerivedNormalSection

universe u

variable {E : Type u} [Group E]

@[expose] def sectionConjugation (N : Subgroup E) [N.Normal] :
    E →* MulAut (derivedNormalSubgroup N) :=
  MulAut.conjNormal

theorem sectionConjugation_apply (N : Subgroup E) [N.Normal]
    (e : E) (h : derivedNormalSubgroup N) :
    (sectionConjugation N e h : E) = e * (h : E) * e⁻¹ :=
  MulAut.conjNormal_apply e h

theorem sectionConjugation_symm_apply (N : Subgroup E) [N.Normal]
    (e : E) (h : derivedNormalSubgroup N) :
    ((sectionConjugation N e).symm h : E) = e⁻¹ * (h : E) * e :=
  MulAut.conjNormal_symm_apply e h

theorem sectionDenominator_conjugation (N Z : Subgroup E) [N.Normal] [Z.Normal] (e : E) :
    (sectionDenominator N Z).map (sectionConjugation N e).toMonoidHom =
      sectionDenominator N Z := by
  ext h
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (sectionConjugation N e x : E) ∈ Z
    rw [sectionConjugation_apply]
    exact (inferInstance : Z.Normal).conj_mem x.val hx e
  · intro hh
    refine ⟨(sectionConjugation N e).symm h, ?_,
      (sectionConjugation N e).apply_symm_apply h⟩
    change ((sectionConjugation N e).symm h : E) ∈ Z
    rw [sectionConjugation_symm_apply]
    simpa only [inv_inv] using
      (inferInstance : Z.Normal).conj_mem h.val hh e⁻¹

@[expose] def sectionAutomorphism (N Z : Subgroup E) [N.Normal] [Z.Normal] (e : E) :
    MulAut (Section N Z) :=
  QuotientGroup.congr (sectionDenominator N Z) (sectionDenominator N Z)
    (sectionConjugation N e) (sectionDenominator_conjugation N Z e)

theorem sectionAutomorphism_mk (N Z : Subgroup E) [N.Normal] [Z.Normal]
    (e : E) (h : derivedNormalSubgroup N) :
    sectionAutomorphism N Z e (sectionProjection N Z h) =
      sectionProjection N Z (sectionConjugation N e h) :=
  QuotientGroup.congr_mk' _ _ _ _ h

theorem sectionAutomorphism_mk_literal (N Z : Subgroup E) [N.Normal] [Z.Normal]
    (e : E) (h : derivedNormalSubgroup N) :
    sectionAutomorphism N Z e (sectionProjection N Z h) =
      sectionProjection N Z
        ⟨e * (h : E) * e⁻¹,
          (inferInstance : (derivedNormalSubgroup N).Normal).conj_mem h.val h.property e⟩ := by
  rw [sectionAutomorphism_mk]
  rfl

theorem sectionAutomorphism_symm_mk (N Z : Subgroup E) [N.Normal] [Z.Normal]
    (e : E) (h : derivedNormalSubgroup N) :
    (sectionAutomorphism N Z e).symm (sectionProjection N Z h) =
      sectionProjection N Z ((sectionConjugation N e).symm h) :=
  rfl

@[expose] def quotientConjugationHom (N Z : Subgroup E) [N.Normal] [Z.Normal] :
    E →* MulAut (Section N Z) where
  toFun := sectionAutomorphism N Z
  map_one' := by
    apply MulEquiv.ext
    intro p
    obtain ⟨h, rfl⟩ := sectionProjection_surjective N Z p
    change sectionAutomorphism N Z 1 (sectionProjection N Z h) = sectionProjection N Z h
    simp only [sectionAutomorphism_mk, map_one, MulAut.one_apply]
  map_mul' e f := by
    apply MulEquiv.ext
    intro p
    obtain ⟨h, rfl⟩ := sectionProjection_surjective N Z p
    change sectionAutomorphism N Z (e * f) (sectionProjection N Z h) =
      sectionAutomorphism N Z e (sectionAutomorphism N Z f (sectionProjection N Z h))
    simp only [sectionAutomorphism_mk, map_mul, MulAut.mul_apply]

theorem quotientConjugationHom_derivedMember (N Z : Subgroup E) [N.Normal] [Z.Normal]
    (h : derivedNormalSubgroup N) :
    quotientConjugationHom N Z (h : E) = MulAut.conj (sectionProjection N Z h) := by
  apply MulEquiv.ext
  intro p
  obtain ⟨x, rfl⟩ := sectionProjection_surjective N Z p
  change sectionAutomorphism N Z (h : E) (sectionProjection N Z x) = _
  rw [sectionAutomorphism_mk]
  change sectionProjection N Z (MulAut.conjNormal (h : E) x) = _
  rw [MulAut.conjNormal_val, MulAut.conj_apply, MulAut.conj_apply,
    map_mul, map_mul, map_inv]

@[expose] def theta (N Z : Subgroup E) [N.Normal] [Z.Normal] :
    E →* OuterAutomorphisms.Outer (Section N Z) :=
  (QuotientGroup.mk' (OuterAutomorphisms.inner (Section N Z))).comp
    (quotientConjugationHom N Z)

theorem theta_apply (N Z : Subgroup E) [N.Normal] [Z.Normal] (e : E) :
    theta N Z e =
      (QuotientGroup.mk' (OuterAutomorphisms.inner (Section N Z)))
        (quotientConjugationHom N Z e) :=
  rfl

theorem theta_kernel (N Z : Subgroup E) [N.Normal] [Z.Normal] :
    (theta N Z).ker =
      (OuterAutomorphisms.inner (Section N Z)).comap (quotientConjugationHom N Z) := by
  ext e
  exact QuotientGroup.eq_one_iff (quotientConjugationHom N Z e)

theorem theta_derivedMember (N Z : Subgroup E) [N.Normal] [Z.Normal]
    (h : derivedNormalSubgroup N) :
    theta N Z (h : E) = 1 := by
  rw [theta_apply]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact ⟨sectionProjection N Z h, (quotientConjugationHom_derivedMember N Z h).symm⟩

theorem derivedNormalSubgroup_le_theta_kernel (N Z : Subgroup E) [N.Normal] [Z.Normal] :
    derivedNormalSubgroup N ≤ (theta N Z).ker := by
  intro h hh
  exact theta_derivedMember N Z ⟨h, hh⟩

end CFSG.ComponentClassification.CatalogueBDerivedNormalSection
