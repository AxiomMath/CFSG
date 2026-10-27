module

public import CFSG.ClassicalGroups.Orthogonal.Lines

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointAction

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

universe u v

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]

@[expose] def Points (Q : QuadraticForm K V) : Type _ :=
  {L : Submodule K V // Module.finrank K L = 1 ∧ ∀ x ∈ L, Q x = 0}

variable (Q : QuadraticForm K V)

@[expose] noncomputable def nativePointEquiv : singularLines Q ≃ Points Q where
  toFun p := ⟨p.val.submodule, p.val.finrank_submodule, by
    intro x hx
    rw [Projectivization.submodule_eq, Submodule.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [map_smul_eq_sq, p.property, mul_zero]⟩
  invFun L := ⟨Projectivization.mk'' L.val L.property.1, by
    apply L.property.2
    have hmem : (Projectivization.mk'' L.val L.property.1).rep ∈
        (Projectivization.mk'' L.val L.property.1).submodule := by
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self _
    simpa only [Projectivization.submodule_mk''] using hmem⟩
  left_inv p := Subtype.ext (Projectivization.mk''_submodule p.val)
  right_inv L := Subtype.ext (Projectivization.submodule_mk'' L.val L.property.1)

theorem nativePointEquiv_submodule (p : singularLines Q) :
    (nativePointEquiv Q p).val = p.val.submodule := rfl

theorem nativePointEquiv_symm_submodule (L : Points Q) :
    ((nativePointEquiv Q).symm L).val.submodule = L.val :=
  Projectivization.submodule_mk'' L.val L.property.1

variable {Q}

@[expose] noncomputable def pointMk (x : V) (hx : x ≠ 0) (hQx : Q x = 0) : Points Q :=
  nativePointEquiv Q (lineMk x hx hQx)

theorem pointMk_submodule (x : V) (hx : x ≠ 0) (hQx : Q x = 0) :
    (pointMk x hx hQx).val = Submodule.span K {x} := rfl

theorem pointMk_eq_iff {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
    (hQx : Q x = 0) (hQy : Q y = 0) :
    pointMk x hx hQx = pointMk y hy hQy ↔ ∃ a : K, a • y = x := by
  rw [pointMk, pointMk, Equiv.apply_eq_iff_eq]
  exact lineMk_eq_lineMk_iff hx hy hQx hQy

theorem exists_eq_pointMk (L : Points Q) :
    ∃ (x : V) (hx : x ≠ 0) (hQx : Q x = 0), L = pointMk x hx hQx := by
  obtain ⟨x, hx, hQx, hL⟩ := exists_eq_lineMk ((nativePointEquiv Q).symm L)
  exact ⟨x, hx, hQx, by rw [pointMk, ← hL, Equiv.apply_symm_apply]⟩

variable (Q)

@[expose] noncomputable def elementaryPointAction :
    elementaryGroup Q →* Equiv.Perm (Points Q) :=
  (nativePointEquiv Q).permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom (elementaryGroup Q) (singularLines Q))

noncomputable instance elementaryMulAction : MulAction (elementaryGroup Q) (Points Q) :=
  MulAction.compHom (Points Q) (elementaryPointAction Q)

theorem nativePointEquiv_smul (g : elementaryGroup Q) (p : singularLines Q) :
    nativePointEquiv Q (g • p) = g • nativePointEquiv Q p := by
  change _ = (nativePointEquiv Q).permCongr
    (MulAction.toPermHom (elementaryGroup Q) (singularLines Q) g) (nativePointEquiv Q p)
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rfl

variable {Q}

theorem smul_pointMk (g : elementaryGroup Q) (x : V) (hx : x ≠ 0) (hQx : Q x = 0) :
    g • pointMk x hx hQx = pointMk ((g : V ≃ₗ[K] V) x)
      (fun h => hx ((g : V ≃ₗ[K] V).map_eq_zero_iff.mp h))
      (by rw [map_of_mem (elementaryGroup_le_orthogonalGroup Q g.property), hQx]) := by
  rw [pointMk, ← nativePointEquiv_smul, smul_lineMk]
  rfl

theorem elementary_smul_submodule (g : elementaryGroup Q) (L : Points Q) :
    (g • L).val = L.val.map ((g : V ≃ₗ[K] V) : V →ₗ[K] V) := by
  obtain ⟨x, hx, hQx, rfl⟩ := exists_eq_pointMk L
  rw [smul_pointMk, pointMk_submodule, pointMk_submodule,
    Submodule.map_span, Set.image_singleton]
  rfl

theorem smul_pointMk_of_apply_eq_smul {g : elementaryGroup Q} {x y : V}
    (hx : x ≠ 0) (hy : y ≠ 0) (hQx : Q x = 0) (hQy : Q y = 0)
    {a : K} (h : (g : V ≃ₗ[K] V) x = a • y) :
    g • pointMk x hx hQx = pointMk y hy hQy := by
  rw [pointMk, ← nativePointEquiv_smul,
    smul_lineMk_of_apply_eq_smul hx hy hQx hQy h]
  rfl

@[expose] def PointPerp (L M : Points Q) : Prop :=
  ∀ x ∈ L.val, ∀ y ∈ M.val, polar Q x y = 0

theorem pointPerp_pointMk {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
    (hQx : Q x = 0) (hQy : Q y = 0) :
    PointPerp (pointMk x hx hQx) (pointMk y hy hQy) ↔ polar Q x y = 0 := by
  constructor
  · intro h
    exact h x (Submodule.mem_span_singleton_self x) y (Submodule.mem_span_singleton_self y)
  · intro h a ha b hb
    rw [pointMk_submodule, Submodule.mem_span_singleton] at ha hb
    obtain ⟨c, rfl⟩ := ha
    obtain ⟨d, rfl⟩ := hb
    rw [polar_smul_left_eq, polar_smul_right_eq, h, mul_zero, mul_zero]

theorem pointPerp_smul_iff (g : elementaryGroup Q) (L M : Points Q) :
    PointPerp (g • L) (g • M) ↔ PointPerp L M := by
  obtain ⟨x, hx, hQx, rfl⟩ := exists_eq_pointMk L
  obtain ⟨y, hy, hQy, rfl⟩ := exists_eq_pointMk M
  rw [smul_pointMk, smul_pointMk, pointPerp_pointMk, pointPerp_pointMk,
    polar_map_of_mem (elementaryGroup_le_orthogonalGroup Q g.property)]

end CFSG.ComponentClassification.CatalogueBOrthogonalPointAction
