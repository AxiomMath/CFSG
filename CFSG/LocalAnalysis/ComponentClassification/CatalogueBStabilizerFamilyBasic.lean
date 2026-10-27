module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.GroupAction.Basic

public section

namespace CFSG.ComponentClassification.CatalogueBStabilizerFamily

open scoped Pointwise

universe u v

variable {G : Type u} [Group G] {X : Type v}

@[expose] def pointStabilizer (rho : G →* Equiv.Perm X) (x : X) : Subgroup G :=
  letI := MulAction.compHom X rho
  MulAction.stabilizer G x

theorem mem_pointStabilizer_iff (rho : G →* Equiv.Perm X) (x : X) (g : G) :
    g ∈ pointStabilizer rho x ↔ rho g x = x := Iff.rfl

@[expose] def family (rho : G →* Equiv.Perm X) : Set (Subgroup G) :=
  Set.range (pointStabilizer rho)

@[expose] def familyAut (rho : G →* Equiv.Perm X) : Subgroup (MulAut G) :=
  MulAction.stabilizer (MulAut G) (family rho)

theorem mem_familyAut_iff (rho : G →* Equiv.Perm X) (alpha : MulAut G) :
    alpha ∈ familyAut rho ↔
      (fun U : Subgroup G => U.map alpha.toMonoidHom) '' family rho = family rho :=
  Iff.rfl

theorem pointStabilizer_conj (rho : G →* Equiv.Perm X) (g : G) (x : X) :
    (pointStabilizer rho x).map (MulAut.conj g).toMonoidHom =
      pointStabilizer rho (rho g x) := by
  let _ := MulAction.compHom X rho
  exact (MulAction.stabilizer_smul_eq_stabilizer_map_conj g x).symm

theorem conj_mem_familyAut (rho : G →* Equiv.Perm X) (g : G) :
    MulAut.conj g ∈ familyAut rho := by
  rw [mem_familyAut_iff]
  ext U
  constructor
  · rintro ⟨V, ⟨x, rfl⟩, rfl⟩
    exact ⟨rho g x, (pointStabilizer_conj rho g x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨pointStabilizer rho (rho g⁻¹ x), ⟨rho g⁻¹ x, rfl⟩, ?_⟩
    change (pointStabilizer rho (rho g⁻¹ x)).map (MulAut.conj g).toMonoidHom =
      pointStabilizer rho x
    rw [pointStabilizer_conj]
    simp

theorem inner_le_familyAut (rho : G →* Equiv.Perm X) :
    (MulAut.conj : G →* MulAut G).range ≤ familyAut rho := by
  rintro alpha ⟨g, rfl⟩
  exact conj_mem_familyAut rho g

theorem exists_image_point (rho : G →* Equiv.Perm X) (alpha : familyAut rho) (x : X) :
    ∃ y : X, (pointStabilizer rho x).map alpha.val.toMonoidHom = pointStabilizer rho y := by
  have h : (pointStabilizer rho x).map alpha.val.toMonoidHom ∈ family rho := by
    rw [← (mem_familyAut_iff rho alpha.val).mp alpha.property]
    exact ⟨pointStabilizer rho x, ⟨x, rfl⟩, rfl⟩
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy.symm⟩

end CFSG.ComponentClassification.CatalogueBStabilizerFamily
