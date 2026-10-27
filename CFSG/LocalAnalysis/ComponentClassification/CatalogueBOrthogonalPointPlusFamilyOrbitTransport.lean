module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBStabilizerFamilyBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbitBasic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit

open scoped Pointwise
open CatalogueBOrthogonalSmallFamilyOrbit

universe u v w

variable {G : Type u} [Group G] {J : Type v} [Group J]

@[expose] def familyTransport (e : G ≃* J) : Set (Subgroup G) ≃ Set (Subgroup J) :=
  e.mapSubgroup.toEquiv.setCongr

theorem familyTransport_apply (e : G ≃* J) (F : Set (Subgroup G)) :
    familyTransport e F = (fun U => U.map e.toMonoidHom) '' F := rfl

theorem familyTransport_symm_apply (e : G ≃* J) (F : Set (Subgroup J)) :
    (familyTransport e).symm F = (fun U => U.map e.symm.toMonoidHom) '' F := rfl

theorem automorphismTransport_apply (e : G ≃* J) (alpha : MulAut G) (x : J) :
    MulAut.congr e alpha x = e (alpha (e.symm x)) := rfl

theorem automorphismTransport_symm_apply (e : G ≃* J) (alpha : MulAut J) (x : G) :
    (MulAut.congr e).symm alpha x = e.symm (alpha (e x)) := rfl

theorem subgroupTransport_automorphism (e : G ≃* J) (U : Subgroup G)
    (alpha : MulAut G) :
    (U.map alpha.toMonoidHom).map e.toMonoidHom =
      (U.map e.toMonoidHom).map (MulAut.congr e alpha).toMonoidHom := by
  have h : e.toMonoidHom.comp alpha.toMonoidHom =
      (MulAut.congr e alpha).toMonoidHom.comp e.toMonoidHom := by
    ext x
    change e (alpha x) = e (alpha (e.symm (e x)))
    rw [e.symm_apply_apply]
  rw [Subgroup.map_map, Subgroup.map_map, h]

theorem automorphismTransport_conj (e : G ≃* J) (g : G) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext x
  change e (g * e.symm x * g⁻¹) = e g * x * (e g)⁻¹
  rw [map_mul, map_mul, map_inv, e.apply_symm_apply]

theorem subgroupTransport_conj (e : G ≃* J) (U : Subgroup G) (g : G) :
    (U.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom =
      (U.map e.toMonoidHom).map (MulAut.conj (e g)).toMonoidHom := by
  rw [subgroupTransport_automorphism, automorphismTransport_conj]

theorem familyTransport_conjugacy (e : G ≃* J) (D : Subgroup G) :
    familyTransport e (conjugacyFamily D) = conjugacyFamily (D.map e.toMonoidHom) := by
  ext U
  constructor
  · rintro ⟨T, ⟨g, rfl⟩, rfl⟩
    exact ⟨e g, (subgroupTransport_conj e D g).symm⟩
  · rintro ⟨g, rfl⟩
    refine ⟨D.map (MulAut.conj (e.symm g)).toMonoidHom, ⟨e.symm g, rfl⟩, ?_⟩
    change (D.map (MulAut.conj (e.symm g)).toMonoidHom).map e.toMonoidHom = _
    rw [subgroupTransport_conj, e.apply_symm_apply]

theorem familyTransport_automorphism (e : G ≃* J) (F : Set (Subgroup G))
    (alpha : MulAut G) :
    familyTransport e (alpha • F) = MulAut.congr e alpha • familyTransport e F := by
  ext U
  constructor
  · rintro ⟨T, ⟨S, hS, rfl⟩, rfl⟩
    refine ⟨S.map e.toMonoidHom, ⟨S, hS, rfl⟩, ?_⟩
    exact (subgroupTransport_automorphism e S alpha).symm
  · rintro ⟨T, ⟨S, hS, rfl⟩, rfl⟩
    refine ⟨S.map alpha.toMonoidHom, ⟨S, hS, rfl⟩, ?_⟩
    exact subgroupTransport_automorphism e S alpha

theorem familyTransport_orbit (e : G ≃* J) (F : Set (Subgroup G)) :
    (familyTransport e) '' MulAction.orbit (MulAut G) F =
      MulAction.orbit (MulAut J) (familyTransport e F) := by
  ext T
  constructor
  · rintro ⟨S, hS, rfl⟩
    obtain ⟨alpha, rfl⟩ := MulAction.mem_orbit_iff.mp hS
    exact MulAction.mem_orbit_iff.mpr
      ⟨MulAut.congr e alpha, (familyTransport_automorphism e F alpha).symm⟩
  · intro hT
    obtain ⟨alpha, rfl⟩ := MulAction.mem_orbit_iff.mp hT
    refine ⟨(MulAut.congr e).symm alpha • F,
      MulAction.mem_orbit F ((MulAut.congr e).symm alpha), ?_⟩
    rw [familyTransport_automorphism, MulEquiv.apply_symm_apply]

theorem familyTransport_mem_orbit_iff (e : G ≃* J) (F T : Set (Subgroup G)) :
    familyTransport e T ∈ MulAction.orbit (MulAut J) (familyTransport e F) ↔
      T ∈ MulAction.orbit (MulAut G) F := by
  rw [← familyTransport_orbit]
  exact (familyTransport e).injective.mem_set_image

@[expose] def familyOrbitTransportEquiv (e : G ≃* J) (D : Subgroup G) :
    FamilyOrbit D ≃ FamilyOrbit (D.map e.toMonoidHom) :=
  (familyTransport e).subtypeEquiv (fun T => by
    rw [← familyTransport_conjugacy e D]
    exact (familyTransport_mem_orbit_iff e (conjugacyFamily D) T).symm)

theorem familyOrbitTransport_card (e : G ≃* J) (D : Subgroup G) :
    Nat.card (FamilyOrbit D) = Nat.card (FamilyOrbit (D.map e.toMonoidHom)) :=
  Nat.card_congr (familyOrbitTransportEquiv e D)

theorem pointStabilizer_comp_equiv_comap {Y : Type w} (rho : J →* Equiv.Perm Y)
    (e : G ≃* J) (x : Y) :
    (CatalogueBStabilizerFamily.pointStabilizer rho x).comap e.toMonoidHom =
      CatalogueBStabilizerFamily.pointStabilizer (rho.comp e.toMonoidHom) x := rfl

theorem pointStabilizer_comp_equiv_map {Y : Type w} (rho : J →* Equiv.Perm Y)
    (e : G ≃* J) (x : Y) :
    (CatalogueBStabilizerFamily.pointStabilizer (rho.comp e.toMonoidHom) x).map
      e.toMonoidHom = CatalogueBStabilizerFamily.pointStabilizer rho x := by
  rw [← pointStabilizer_comp_equiv_comap]
  exact Subgroup.map_comap_eq_self_of_surjective e.surjective _

theorem pointFamily_comp_equiv_transport {Y : Type w} (rho : J →* Equiv.Perm Y)
    (e : G ≃* J) :
    familyTransport e (CatalogueBStabilizerFamily.family (rho.comp e.toMonoidHom)) =
      CatalogueBStabilizerFamily.family rho := by
  ext U
  constructor
  · rintro ⟨T, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (pointStabilizer_comp_equiv_map rho e x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨CatalogueBStabilizerFamily.pointStabilizer (rho.comp e.toMonoidHom) x,
      ⟨x, rfl⟩, pointStabilizer_comp_equiv_map rho e x⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
