module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBStabilizerFamilyCovariance

public section

namespace CFSG.ComponentClassification.CatalogueBStabilizerFamily

universe u v

variable {G : Type u} [Group G] {X : Type v}

@[expose] def imageNormalizer (rho : G →* Equiv.Perm X) : Subgroup (Equiv.Perm X) :=
  Subgroup.normalizer (rho.range : Set (Equiv.Perm X))

theorem range_le_imageNormalizer (rho : G →* Equiv.Perm X) :
    rho.range ≤ imageNormalizer rho := Subgroup.le_normalizer

theorem pointPerm_mem_imageNormalizer (rho : G →* Equiv.Perm X)
    (hs : Function.Injective (pointStabilizer rho)) (alpha : familyAut rho) :
    pointPerm rho hs alpha ∈ imageNormalizer rho :=
  covariance_normalizer rho alpha.val (pointPerm rho hs alpha)
    (pointPerm_covariance rho hs alpha)

@[expose] noncomputable def normalizerHom (rho : G →* Equiv.Perm X)
    (hs : Function.Injective (pointStabilizer rho)) :
    familyAut rho →* imageNormalizer rho :=
  (permutationHom rho hs).codRestrict (imageNormalizer rho)
    (pointPerm_mem_imageNormalizer rho hs)

@[expose] def rangeConjugation (rho : G →* Equiv.Perm X) (phi : imageNormalizer rho) :
    MulAut rho.range :=
  ((MulAut.conj phi.val).subgroupMap rho.range).trans
    (MulEquiv.subgroupCongr (Subgroup.mem_normalizer_iff_map_conj_eq.mp phi.property))

theorem rangeConjugation_apply (rho : G →* Equiv.Perm X)
    (phi : imageNormalizer rho) (p : rho.range) :
    (rangeConjugation rho phi p).val = phi.val * p.val * phi.val⁻¹ := by
  simp [rangeConjugation]

@[expose] noncomputable def inducedAut (rho : G →* Equiv.Perm X)
    (hrho : Function.Injective rho) (phi : imageNormalizer rho) : MulAut G :=
  ((MonoidHom.ofInjective hrho).trans (rangeConjugation rho phi)).trans
    (MonoidHom.ofInjective hrho).symm

theorem inducedAut_covariance (rho : G →* Equiv.Perm X)
    (hrho : Function.Injective rho) (phi : imageNormalizer rho) (g : G) :
    phi.val * rho g * phi.val⁻¹ = rho (inducedAut rho hrho phi g) := by
  simp [inducedAut, rangeConjugation_apply, MonoidHom.ofInjective_apply]

@[expose] noncomputable def normalizerAut (rho : G →* Equiv.Perm X)
    (hrho : Function.Injective rho) (phi : imageNormalizer rho) : familyAut rho :=
  ⟨inducedAut rho hrho phi,
    covariance_familyAut rho (inducedAut rho hrho phi) phi.val
      (inducedAut_covariance rho hrho phi)⟩

theorem pointPerm_normalizerAut (rho : G →* Equiv.Perm X)
    (hrho : Function.Injective rho) (hs : Function.Injective (pointStabilizer rho))
    (phi : imageNormalizer rho) :
    pointPerm rho hs (normalizerAut rho hrho phi) = phi.val :=
  pointPerm_of_covariance rho hs (inducedAut rho hrho phi) phi.val
    (inducedAut_covariance rho hrho phi)

theorem normalizerHom_injective (rho : G →* Equiv.Perm X)
    (hrho : Function.Injective rho) (hs : Function.Injective (pointStabilizer rho)) :
    Function.Injective (normalizerHom rho hs) := by
  intro alpha beta h
  exact permutationHom_injective rho hrho hs (congrArg Subtype.val h)

theorem normalizerHom_surjective (rho : G →* Equiv.Perm X)
    (hrho : Function.Injective rho) (hs : Function.Injective (pointStabilizer rho)) :
    Function.Surjective (normalizerHom rho hs) := by
  intro phi
  refine ⟨normalizerAut rho hrho phi, ?_⟩
  apply Subtype.ext
  exact pointPerm_normalizerAut rho hrho hs phi

@[expose] noncomputable def normalizerEquiv (rho : G →* Equiv.Perm X)
    (hrho : Function.Injective rho) (hs : Function.Injective (pointStabilizer rho)) :
    familyAut rho ≃* imageNormalizer rho :=
  MulEquiv.ofBijective (normalizerHom rho hs)
    ⟨normalizerHom_injective rho hrho hs, normalizerHom_surjective rho hrho hs⟩

theorem normalizerEquiv_apply (rho : G →* Equiv.Perm X)
    (hrho : Function.Injective rho) (hs : Function.Injective (pointStabilizer rho))
    (alpha : familyAut rho) :
    (normalizerEquiv rho hrho hs alpha).val = pointPerm rho hs alpha := rfl

theorem normalizerEquiv_symm_apply (rho : G →* Equiv.Perm X)
    (hrho : Function.Injective rho) (hs : Function.Injective (pointStabilizer rho))
    (phi : imageNormalizer rho) :
    (normalizerEquiv rho hrho hs).symm phi = normalizerAut rho hrho phi := by
  apply (normalizerEquiv rho hrho hs).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  exact (pointPerm_normalizerAut rho hrho hs phi).symm

theorem normalizerEquiv_stabilizer (rho : G →* Equiv.Perm X)
    (hrho : Function.Injective rho) (hs : Function.Injective (pointStabilizer rho))
    (alpha : familyAut rho) (x : X) :
    (pointStabilizer rho x).map alpha.val.toMonoidHom =
      pointStabilizer rho ((normalizerEquiv rho hrho hs alpha).val x) :=
  pointPerm_stabilizer rho hs alpha x

theorem normalizerEquiv_covariance (rho : G →* Equiv.Perm X)
    (hrho : Function.Injective rho) (hs : Function.Injective (pointStabilizer rho))
    (alpha : familyAut rho) (g : G) :
    (normalizerEquiv rho hrho hs alpha).val * rho g *
        (normalizerEquiv rho hrho hs alpha).val⁻¹ = rho (alpha.val g) :=
  pointPerm_covariance rho hs alpha g

end CFSG.ComponentClassification.CatalogueBStabilizerFamily
