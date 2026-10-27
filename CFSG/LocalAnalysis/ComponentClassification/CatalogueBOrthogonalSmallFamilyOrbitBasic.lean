module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit

open scoped Pointwise

universe u

variable {G : Type u} [Group G]

@[expose] def conjugacyFamily (H : Subgroup G) : Set (Subgroup G) :=
  Set.range (fun g : G => H.map (MulAut.conj g).toMonoidHom)

@[expose] def familyStabilizer (H : Subgroup G) : Subgroup (MulAut G) :=
  MulAction.stabilizer (MulAut G) (conjugacyFamily H)

theorem mem_familyStabilizer_iff (H : Subgroup G) (alpha : MulAut G) :
    alpha ∈ familyStabilizer H ↔
      (fun U : Subgroup G => U.map alpha.toMonoidHom) '' conjugacyFamily H =
        conjugacyFamily H := Iff.rfl

theorem subgroup_conj_covariance (H : Subgroup G) (alpha : MulAut G) (g : G) :
    (H.map (MulAut.conj g).toMonoidHom).map alpha.toMonoidHom =
      (H.map alpha.toMonoidHom).map (MulAut.conj (alpha g)).toMonoidHom := by
  have hcomp : alpha.toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (alpha g)).toMonoidHom.comp alpha.toMonoidHom := by
    ext x
    change alpha (g * x * g⁻¹) = alpha g * alpha x * (alpha g)⁻¹
    rw [map_mul, map_mul, map_inv]
  rw [Subgroup.map_map, Subgroup.map_map, hcomp]

theorem conjugacyFamily_covariance (H : Subgroup G) (alpha : MulAut G) :
    alpha • conjugacyFamily H = conjugacyFamily (H.map alpha.toMonoidHom) := by
  ext U
  constructor
  · rintro ⟨W, ⟨g, rfl⟩, rfl⟩
    exact ⟨alpha g, (subgroup_conj_covariance H alpha g).symm⟩
  · rintro ⟨g, rfl⟩
    refine ⟨H.map (MulAut.conj (alpha.symm g)).toMonoidHom,
      ⟨alpha.symm g, rfl⟩, ?_⟩
    change (H.map (MulAut.conj (alpha.symm g)).toMonoidHom).map alpha.toMonoidHom = _
    rw [subgroup_conj_covariance, alpha.apply_symm_apply]

theorem conj_conjugacyFamily (H : Subgroup G) (g : G) :
    MulAut.conj g • conjugacyFamily H = conjugacyFamily H := by
  ext U
  constructor
  · rintro ⟨W, ⟨h, rfl⟩, rfl⟩
    refine ⟨g * h, ?_⟩
    change MulAut.conj (g * h) • H = MulAut.conj g • (MulAut.conj h • H)
    rw [map_mul, mul_smul]
  · rintro ⟨h, rfl⟩
    refine ⟨MulAut.conj (g⁻¹ * h) • H, ⟨g⁻¹ * h, rfl⟩, ?_⟩
    change MulAut.conj g • (MulAut.conj (g⁻¹ * h) • H) = MulAut.conj h • H
    rw [← mul_smul, ← map_mul]
    simp

abbrev FamilyOrbit (H : Subgroup G) :=
  {F' : Set (Subgroup G) // F' ∈ MulAction.orbit (MulAut G) (conjugacyFamily H)}

@[expose] def familyOrbitBase (H : Subgroup G) : FamilyOrbit H :=
  ⟨conjugacyFamily H, MulAction.mem_orbit_self _⟩

instance familyOrbitFinite [Finite G] (H : Subgroup G) : Finite (FamilyOrbit H) :=
  (Finite.finite_mulAction_orbit (M := MulAut G) (conjugacyFamily H)).to_subtype

@[expose] def familyOrbitAction (H : Subgroup G) :
    MulAut G →* Equiv.Perm (FamilyOrbit H) :=
  MulAction.toPermHom (MulAut G) (FamilyOrbit H)

@[expose] def orbitKernel (H : Subgroup G) : Subgroup (MulAut G) :=
  (familyOrbitAction H).ker

instance orbitKernelNormal (H : Subgroup G) : (orbitKernel H).Normal :=
  MonoidHom.normal_ker _

theorem mem_orbitKernel_iff (H : Subgroup G) (alpha : MulAut G) :
    alpha ∈ orbitKernel H ↔ ∀ F' : FamilyOrbit H, alpha • F'.val = F'.val := by
  change familyOrbitAction H alpha = 1 ↔ _
  constructor
  · intro h F'
    exact congrArg (fun p : Equiv.Perm (FamilyOrbit H) => (p F').val) h
  · intro h
    apply Equiv.ext
    intro F'
    exact Subtype.ext (h F')

theorem inner_le_orbitKernel (H : Subgroup G) :
    OuterAutomorphisms.inner G ≤ orbitKernel H := by
  rintro alpha ⟨g, rfl⟩
  rw [mem_orbitKernel_iff]
  intro F'
  obtain ⟨beta, hbeta⟩ := MulAction.mem_orbit_iff.mp F'.property
  rw [← hbeta, conjugacyFamily_covariance]
  exact conj_conjugacyFamily _ g

theorem orbitKernel_le_familyStabilizer (H : Subgroup G) :
    orbitKernel H ≤ familyStabilizer H := by
  intro alpha halpha
  exact (mem_orbitKernel_iff H alpha).mp halpha (familyOrbitBase H)

theorem inner_le_familyStabilizer (H : Subgroup G) :
    OuterAutomorphisms.inner G ≤ familyStabilizer H :=
  (inner_le_orbitKernel H).trans (orbitKernel_le_familyStabilizer H)

@[expose] noncomputable def familyInner (H : Subgroup G) : Subgroup (familyStabilizer H) :=
  (OuterAutomorphisms.inner G).subgroupOf (familyStabilizer H)

instance familyInnerNormal (H : Subgroup G) : (familyInner H).Normal :=
  (OuterAutomorphisms.inner_normal G).subgroupOf _

abbrev FamilyOuter (H : Subgroup G) := familyStabilizer H ⧸ familyInner H

@[expose] noncomputable def kernelInner (H : Subgroup G) : Subgroup (orbitKernel H) :=
  (OuterAutomorphisms.inner G).subgroupOf (orbitKernel H)

instance kernelInnerNormal (H : Subgroup G) : (kernelInner H).Normal :=
  (OuterAutomorphisms.inner_normal G).subgroupOf _

abbrev KernelOuter (H : Subgroup G) := orbitKernel H ⧸ kernelInner H

end CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
