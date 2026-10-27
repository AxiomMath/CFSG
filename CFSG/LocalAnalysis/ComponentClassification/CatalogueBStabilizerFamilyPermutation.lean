module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBStabilizerFamilyBasic

public section

namespace CFSG.ComponentClassification.CatalogueBStabilizerFamily

open scoped Pointwise

universe u v

variable {G : Type u} [Group G] {X : Type v}

@[expose] noncomputable def imagePoint (rho : G →* Equiv.Perm X)
    (alpha : familyAut rho) (x : X) : X :=
  Classical.choose (exists_image_point rho alpha x)

theorem imagePoint_spec (rho : G →* Equiv.Perm X) (alpha : familyAut rho) (x : X) :
    (pointStabilizer rho x).map alpha.val.toMonoidHom =
      pointStabilizer rho (imagePoint rho alpha x) :=
  Classical.choose_spec (exists_image_point rho alpha x)

theorem imagePoint_inv (rho : G →* Equiv.Perm X)
    (hs : Function.Injective (pointStabilizer rho)) (alpha : familyAut rho) (x : X) :
    imagePoint rho alpha⁻¹ (imagePoint rho alpha x) = x := by
  apply hs
  rw [← imagePoint_spec, ← imagePoint_spec]
  change alpha.val⁻¹ • (alpha.val • pointStabilizer rho x) = pointStabilizer rho x
  exact inv_smul_smul alpha.val (pointStabilizer rho x)

@[expose] noncomputable def pointPerm (rho : G →* Equiv.Perm X)
    (hs : Function.Injective (pointStabilizer rho)) (alpha : familyAut rho) :
    Equiv.Perm X where
  toFun := imagePoint rho alpha
  invFun := imagePoint rho alpha⁻¹
  left_inv := imagePoint_inv rho hs alpha
  right_inv x := by
    simpa using imagePoint_inv rho hs alpha⁻¹ x

theorem pointPerm_stabilizer (rho : G →* Equiv.Perm X)
    (hs : Function.Injective (pointStabilizer rho)) (alpha : familyAut rho) (x : X) :
    (pointStabilizer rho x).map alpha.val.toMonoidHom =
      pointStabilizer rho (pointPerm rho hs alpha x) := imagePoint_spec rho alpha x

theorem pointPerm_unique (rho : G →* Equiv.Perm X)
    (hs : Function.Injective (pointStabilizer rho)) (alpha : familyAut rho)
    (phi : Equiv.Perm X)
    (hphi : ∀ x, (pointStabilizer rho x).map alpha.val.toMonoidHom =
      pointStabilizer rho (phi x)) : phi = pointPerm rho hs alpha := by
  ext x
  exact hs ((hphi x).symm.trans (pointPerm_stabilizer rho hs alpha x))

theorem pointPerm_mul (rho : G →* Equiv.Perm X)
    (hs : Function.Injective (pointStabilizer rho)) (alpha beta : familyAut rho) :
    pointPerm rho hs (alpha * beta) = pointPerm rho hs alpha * pointPerm rho hs beta := by
  apply Eq.symm
  apply pointPerm_unique
  intro x
  calc
    (pointStabilizer rho x).map (alpha * beta).val.toMonoidHom =
        alpha.val • (beta.val • pointStabilizer rho x) :=
      mul_smul alpha.val beta.val (pointStabilizer rho x)
    _ = pointStabilizer rho (pointPerm rho hs alpha (pointPerm rho hs beta x)) := by
      change ((pointStabilizer rho x).map beta.val.toMonoidHom).map
        alpha.val.toMonoidHom = _
      rw [pointPerm_stabilizer rho hs beta, pointPerm_stabilizer rho hs alpha]

theorem pointPerm_one (rho : G →* Equiv.Perm X)
    (hs : Function.Injective (pointStabilizer rho)) : pointPerm rho hs 1 = 1 := by
  apply Eq.symm
  apply pointPerm_unique
  intro x
  change (1 : MulAut G) • pointStabilizer rho x = pointStabilizer rho x
  exact one_smul (MulAut G) (pointStabilizer rho x)

@[expose] noncomputable def permutationHom (rho : G →* Equiv.Perm X)
    (hs : Function.Injective (pointStabilizer rho)) : familyAut rho →* Equiv.Perm X where
  toFun := pointPerm rho hs
  map_one' := pointPerm_one rho hs
  map_mul' := pointPerm_mul rho hs

theorem pointPerm_equivariant (rho : G →* Equiv.Perm X)
    (hs : Function.Injective (pointStabilizer rho)) (alpha : familyAut rho) (g : G) (x : X) :
    pointPerm rho hs alpha (rho g x) = rho (alpha.val g) (pointPerm rho hs alpha x) := by
  apply hs
  rw [← pointPerm_stabilizer, ← pointStabilizer_conj,
    ← pointStabilizer_conj, ← pointPerm_stabilizer]
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext h
  simp

theorem pointPerm_covariance (rho : G →* Equiv.Perm X)
    (hs : Function.Injective (pointStabilizer rho)) (alpha : familyAut rho) (g : G) :
    pointPerm rho hs alpha * rho g * (pointPerm rho hs alpha)⁻¹ = rho (alpha.val g) := by
  ext x
  change pointPerm rho hs alpha (rho g ((pointPerm rho hs alpha)⁻¹ x)) =
    rho (alpha.val g) x
  rw [pointPerm_equivariant]
  simp

theorem permutationHom_injective (rho : G →* Equiv.Perm X)
    (hrho : Function.Injective rho) (hs : Function.Injective (pointStabilizer rho)) :
    Function.Injective (permutationHom rho hs) := by
  intro alpha beta h
  apply Subtype.ext
  ext g
  apply hrho
  rw [← pointPerm_covariance rho hs alpha, ← pointPerm_covariance rho hs beta]
  exact congrArg (fun phi : Equiv.Perm X => phi * rho g * phi⁻¹) h

end CFSG.ComponentClassification.CatalogueBStabilizerFamily
