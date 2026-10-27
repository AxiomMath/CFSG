module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBStabilizerFamilyNormalizer

public section

namespace CFSG.ComponentClassification.CatalogueBStabilizerFamily

universe u v w

variable {G : Type u} [Group G] {X : Type v} {Gamma : Type w} [Group Gamma]

theorem compatible_aut_range (rho : G →* Equiv.Perm X)
    (kappa : Gamma →* MulAut G) (eta : Gamma →* Equiv.Perm X)
    (hcov : ∀ t g, eta t * rho g * (eta t)⁻¹ = rho (kappa t g)) :
    kappa.range ≤ familyAut rho := by
  rintro alpha ⟨t, rfl⟩
  exact covariance_familyAut rho (kappa t) (eta t) (hcov t)

theorem compatible_perm_range (rho : G →* Equiv.Perm X)
    (kappa : Gamma →* MulAut G) (eta : Gamma →* Equiv.Perm X)
    (hcov : ∀ t g, eta t * rho g * (eta t)⁻¹ = rho (kappa t g)) :
    eta.range ≤ imageNormalizer rho := by
  rintro phi ⟨t, rfl⟩
  exact covariance_normalizer rho (kappa t) (eta t) (hcov t)

@[expose] def compatibleAutHom (rho : G →* Equiv.Perm X)
    (kappa : Gamma →* MulAut G) (eta : Gamma →* Equiv.Perm X)
    (hcov : ∀ t g, eta t * rho g * (eta t)⁻¹ = rho (kappa t g)) :
    Gamma →* familyAut rho :=
  kappa.codRestrict (familyAut rho)
    (fun t => covariance_familyAut rho (kappa t) (eta t) (hcov t))

@[expose] def compatiblePermHom (rho : G →* Equiv.Perm X)
    (kappa : Gamma →* MulAut G) (eta : Gamma →* Equiv.Perm X)
    (hcov : ∀ t g, eta t * rho g * (eta t)⁻¹ = rho (kappa t g)) :
    Gamma →* imageNormalizer rho :=
  eta.codRestrict (imageNormalizer rho)
    (fun t => covariance_normalizer rho (kappa t) (eta t) (hcov t))

theorem normalizerEquiv_compatible (rho : G →* Equiv.Perm X)
    (hrho : Function.Injective rho) (hs : Function.Injective (pointStabilizer rho))
    (kappa : Gamma →* MulAut G) (eta : Gamma →* Equiv.Perm X)
    (hcov : ∀ t g, eta t * rho g * (eta t)⁻¹ = rho (kappa t g)) (t : Gamma) :
    normalizerEquiv rho hrho hs (compatibleAutHom rho kappa eta hcov t) =
      compatiblePermHom rho kappa eta hcov t := by
  apply Subtype.ext
  exact pointPerm_of_covariance rho hs (kappa t) (eta t) (hcov t)

theorem compatible_image (rho : G →* Equiv.Perm X)
    (hrho : Function.Injective rho) (hs : Function.Injective (pointStabilizer rho))
    (kappa : Gamma →* MulAut G) (eta : Gamma →* Equiv.Perm X)
    (hcov : ∀ t g, eta t * rho g * (eta t)⁻¹ = rho (kappa t g)) :
    (kappa.range.subgroupOf (familyAut rho)).map
        (normalizerEquiv rho hrho hs).toMonoidHom =
      eta.range.subgroupOf (imageNormalizer rho) := by
  ext phi
  constructor
  · rintro ⟨alpha, ha, rfl⟩
    obtain ⟨t, ht⟩ := ha
    have halpha : alpha = compatibleAutHom rho kappa eta hcov t := Subtype.ext ht.symm
    change (normalizerEquiv rho hrho hs alpha).val ∈ eta.range
    rw [halpha, normalizerEquiv_compatible]
    exact ⟨t, rfl⟩
  · intro hphi
    obtain ⟨t, ht⟩ := hphi
    refine ⟨compatibleAutHom rho kappa eta hcov t, ⟨t, rfl⟩, ?_⟩
    apply Subtype.ext
    exact congrArg Subtype.val (normalizerEquiv_compatible rho hrho hs kappa eta hcov t) |>.trans ht

theorem compatible_image_ambient (rho : G →* Equiv.Perm X)
    (hrho : Function.Injective rho) (hs : Function.Injective (pointStabilizer rho))
    (kappa : Gamma →* MulAut G) (eta : Gamma →* Equiv.Perm X)
    (hcov : ∀ t g, eta t * rho g * (eta t)⁻¹ = rho (kappa t g)) :
    (kappa.range.subgroupOf (familyAut rho)).map
        ((imageNormalizer rho).subtype.comp (normalizerEquiv rho hrho hs).toMonoidHom) =
      eta.range := by
  rw [← Subgroup.map_map, compatible_image rho hrho hs kappa eta hcov]
  exact Subgroup.map_subgroupOf_eq_of_le (compatible_perm_range rho kappa eta hcov)

end CFSG.ComponentClassification.CatalogueBStabilizerFamily
