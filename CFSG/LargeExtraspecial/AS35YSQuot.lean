module

public import CFSG.LargeExtraspecial.OrthoF2PairsCases

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35YS

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

section Quotient

variable (q : QuadraticForm (ZMod 2) V) (U : Submodule (ZMod 2) V)

abbrev radU : Submodule (ZMod 2) U :=
  (LinearMap.BilinForm.orthogonal q.polarBilin U).comap U.subtype

abbrev Quo : Type _ := U ⧸ radU q U

abbrev qU : QuadraticForm (ZMod 2) U := q.comp U.subtype

variable {q U}

theorem mem_radU {x : U} : x ∈ radU q U ↔ ∀ u ∈ U, polar q x u = 0 :=
  OrthoF2.mem_orthogonal_iff_polar

theorem polar_qU (x y : U) : polar (qU q U) x y = polar q x y := by
  simp [polar]

theorem radU_le_radical (h : ∀ v ∈ U, (∀ u ∈ U, polar q v u = 0) → q v = 0) :
    radU q U ≤ (qU q U).radical := by
  intro x hx
  have hx' := mem_radU.mp hx
  refine ⟨h x x.2 hx', ?_⟩
  ext y
  rw [polarBilin_apply_apply, polar_qU]
  exact hx' y y.2

@[expose] noncomputable def qQuo (h : ∀ v ∈ U, (∀ u ∈ U, polar q v u = 0) → q v = 0) :
    QuadraticForm (ZMod 2) (Quo q U) :=
  (qU q U).lift (radU q U) (radU_le_radical h)

variable (h : ∀ v ∈ U, (∀ u ∈ U, polar q v u = 0) → q v = 0)

@[simp] theorem qQuo_mk (u : U) : qQuo h (Submodule.Quotient.mk u) = q u :=
  rfl

theorem polar_qQuo_mk (u u' : U) :
    polar (qQuo h) (Submodule.Quotient.mk u) (Submodule.Quotient.mk u') = polar q u u' := by
  rw [polar, ← Submodule.Quotient.mk_add, qQuo_mk, qQuo_mk, qQuo_mk, Submodule.coe_add]
  rfl

theorem qQuo_nondegenerate : (qQuo h).polarBilin.Nondegenerate := by
  have hsep : ∀ x : Quo q U, (∀ y, polar (qQuo h) x y = 0) → x = 0 := by
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ u =>
      rw [Submodule.Quotient.mk_eq_zero, mem_radU]
      intro u' hu'
      have := hx (Submodule.Quotient.mk ⟨u', hu'⟩)
      rwa [polar_qQuo_mk] at this
  refine ⟨fun x hx => hsep x fun y => ?_, fun x hx => hsep x fun y => ?_⟩
  · simpa [polarBilin_apply_apply] using hx y
  · rw [polar_comm]
    simpa [polarBilin_apply_apply] using hx y

end Quotient

section Action

variable {q : QuadraticForm (ZMod 2) V} {U : Submodule (ZMod 2) V}

theorem polar_map_YS {g : V ≃ₗ[ZMod 2] V} (hiso : ∀ v, q (g v) = q v) (a b : V) :
    polar q (g a) (g b) = polar q a b := by
  simp only [polar, ← map_add, hiso]

theorem map_mem_radU {g : V ≃ₗ[ZMod 2] V} (hiso : ∀ v, q (g v) = q v)
    (hU' : ∀ u ∈ U, g.symm u ∈ U) {x : V} (hx : ∀ u ∈ U, polar q x u = 0) :
    ∀ u ∈ U, polar q (g x) u = 0 := by
  intro u hu
  have e : polar q (g x) u = polar q (g x) (g (g.symm u)) := by rw [g.apply_symm_apply]
  rw [e, polar_map_YS hiso]
  exact hx _ (hU' u hu)

variable (q U)

@[expose] noncomputable def quoLin (g : V ≃ₗ[ZMod 2] V) (hiso : ∀ v, q (g v) = q v)
    (hU : ∀ u ∈ U, g u ∈ U) (hU' : ∀ u ∈ U, g.symm u ∈ U) : Quo q U →ₗ[ZMod 2] Quo q U :=
  (radU q U).mapQ (radU q U) ((g : V →ₗ[ZMod 2] V).restrict hU) fun x hx => by
    rw [Submodule.mem_comap, mem_radU]
    exact map_mem_radU hiso hU' (mem_radU.mp hx)

variable {q U}

@[simp] theorem quoLin_mk (g : V ≃ₗ[ZMod 2] V) (hiso : ∀ v, q (g v) = q v)
    (hU : ∀ u ∈ U, g u ∈ U) (hU' : ∀ u ∈ U, g.symm u ∈ U) (u : U) :
    quoLin q U g hiso hU hU' (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk ⟨g u, hU u u.2⟩ :=
  rfl

variable (q U)

@[expose] noncomputable def quoHom (H : Subgroup (V ≃ₗ[ZMod 2] V))
    (hiso : ∀ g ∈ H, ∀ v, q (g v) = q v) (hU : ∀ g ∈ H, ∀ u ∈ U, g u ∈ U) :
    H →* (Quo q U ≃ₗ[ZMod 2] Quo q U) where
  toFun g :=
    { toLinearMap := quoLin q U g (hiso g g.2) (hU g g.2) (hU _ (H.inv_mem g.2))
      invFun := quoLin q U (g⁻¹ : H) (hiso _ (H.inv_mem g.2)) (hU _ (H.inv_mem g.2))
        (fun u hu => hU g g.2 u hu)
      left_inv := fun x => by
        induction x using Submodule.Quotient.induction_on with
        | _ u =>
          change quoLin q U (g⁻¹ : H) _ _ _ (quoLin q U g _ _ _ (Submodule.Quotient.mk u)) = _
          rw [quoLin_mk, quoLin_mk]
          congr 1
          exact Subtype.ext ((g : V ≃ₗ[ZMod 2] V).symm_apply_apply u)
      right_inv := fun x => by
        induction x using Submodule.Quotient.induction_on with
        | _ u =>
          change quoLin q U g _ _ _ (quoLin q U (g⁻¹ : H) _ _ _ (Submodule.Quotient.mk u)) = _
          rw [quoLin_mk, quoLin_mk]
          congr 1
          exact Subtype.ext ((g : V ≃ₗ[ZMod 2] V).apply_symm_apply u) }
  map_one' := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | _ u => rfl
  map_mul' g g' := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | _ u => rfl

variable {q U}

@[simp] theorem quoHom_mk {H : Subgroup (V ≃ₗ[ZMod 2] V)} {hiso : ∀ g ∈ H, ∀ v, q (g v) = q v}
    {hU : ∀ g ∈ H, ∀ u ∈ U, g u ∈ U} (g : H) (u : U) :
    quoHom q U H hiso hU g (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk ⟨(g : V ≃ₗ[ZMod 2] V) u, hU g g.2 u u.2⟩ :=
  rfl

theorem qQuo_quoHom (h : ∀ v ∈ U, (∀ u ∈ U, polar q v u = 0) → q v = 0)
    {H : Subgroup (V ≃ₗ[ZMod 2] V)} {hiso : ∀ g ∈ H, ∀ v, q (g v) = q v}
    {hU : ∀ g ∈ H, ∀ u ∈ U, g u ∈ U} (g : H) (x : Quo q U) :
    qQuo h (quoHom q U H hiso hU g x) = qQuo h x := by
  induction x using Submodule.Quotient.induction_on with
  | _ u =>
    rw [quoHom_mk, qQuo_mk, qQuo_mk]
    exact hiso g g.2 u

end Action

end CFSG.LargeExtraspecial.AS35YS
