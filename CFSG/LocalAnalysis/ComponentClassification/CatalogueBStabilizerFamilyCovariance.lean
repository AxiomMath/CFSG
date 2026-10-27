module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBStabilizerFamilyPermutation

public section

namespace CFSG.ComponentClassification.CatalogueBStabilizerFamily

universe u v

variable {G : Type u} [Group G] {X : Type v}

theorem covariance_equivariant (rho : G →* Equiv.Perm X)
    (alpha : MulAut G) (phi : Equiv.Perm X)
    (hcov : ∀ g, phi * rho g * phi⁻¹ = rho (alpha g)) (g : G) (x : X) :
    phi (rho g x) = rho (alpha g) (phi x) := by
  have h := congrArg (fun p : Equiv.Perm X => p (phi x)) (hcov g)
  simpa using h

theorem covariance_stabilizer (rho : G →* Equiv.Perm X)
    (alpha : MulAut G) (phi : Equiv.Perm X)
    (hcov : ∀ g, phi * rho g * phi⁻¹ = rho (alpha g)) (x : X) :
    (pointStabilizer rho x).map alpha.toMonoidHom = pointStabilizer rho (phi x) := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_pointStabilizer_iff, mem_pointStabilizer_iff]
  have h := covariance_equivariant rho alpha phi hcov (alpha.symm g) x
  simp only [alpha.apply_symm_apply] at h
  constructor
  · intro hg
    rw [hg] at h
    exact h.symm
  · intro hg
    apply phi.injective
    exact h.trans hg

theorem covariance_familyAut (rho : G →* Equiv.Perm X)
    (alpha : MulAut G) (phi : Equiv.Perm X)
    (hcov : ∀ g, phi * rho g * phi⁻¹ = rho (alpha g)) : alpha ∈ familyAut rho := by
  rw [mem_familyAut_iff]
  ext U
  constructor
  · rintro ⟨V, ⟨x, rfl⟩, rfl⟩
    exact ⟨phi x, (covariance_stabilizer rho alpha phi hcov x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨pointStabilizer rho (phi⁻¹ x), ⟨phi⁻¹ x, rfl⟩, ?_⟩
    change (pointStabilizer rho (phi⁻¹ x)).map alpha.toMonoidHom = _
    rw [covariance_stabilizer rho alpha phi hcov]
    simp

theorem covariance_normalizer (rho : G →* Equiv.Perm X)
    (alpha : MulAut G) (phi : Equiv.Perm X)
    (hcov : ∀ g, phi * rho g * phi⁻¹ = rho (alpha g)) :
    phi ∈ Subgroup.normalizer (rho.range : Set (Equiv.Perm X)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro p
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨alpha g, (hcov g).symm⟩
  · rintro ⟨g, hg⟩
    refine ⟨alpha.symm g, ?_⟩
    have h := hcov (alpha.symm g)
    simp only [alpha.apply_symm_apply] at h
    have he : phi * rho (alpha.symm g) * phi⁻¹ = phi * p * phi⁻¹ := h.trans hg
    exact mul_left_cancel (mul_right_cancel he)

theorem pointPerm_of_covariance (rho : G →* Equiv.Perm X)
    (hs : Function.Injective (pointStabilizer rho)) (alpha : MulAut G) (phi : Equiv.Perm X)
    (hcov : ∀ g, phi * rho g * phi⁻¹ = rho (alpha g)) :
    pointPerm rho hs ⟨alpha, covariance_familyAut rho alpha phi hcov⟩ = phi := by
  exact (pointPerm_unique rho hs _ phi (covariance_stabilizer rho alpha phi hcov)).symm

theorem pointPerm_conj (rho : G →* Equiv.Perm X)
    (hs : Function.Injective (pointStabilizer rho)) (g : G) :
    pointPerm rho hs ⟨MulAut.conj g, conj_mem_familyAut rho g⟩ = rho g := by
  apply Eq.symm
  apply pointPerm_unique
  exact pointStabilizer_conj rho g

end CFSG.ComponentClassification.CatalogueBStabilizerFamily
