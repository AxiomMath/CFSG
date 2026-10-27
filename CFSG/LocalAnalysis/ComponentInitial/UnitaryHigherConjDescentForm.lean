module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherConjDescentFixed
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian
public import TauCeti.LinearAlgebra.BilinearForm.Isometry
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.WittVector.IsPoly

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Module
open LinearMap (BilinForm)

variable {r e : ℕ} {E : Type} [Field E] {h : UnitaryFieldData r e E}
  {V : Type} [AddCommGroup V] [Module E V]

section Form

variable (Hf : V →ₛₗ[h.bar] V →ₗ[E] E) (τ : V →ₛₗ[h.bar] V) (c : E)
  (hc : ∀ v w, v ∈ conjFixed h τ → w ∈ conjFixed h τ → h.bar (c * Hf v w) = c * Hf v w)

@[expose] noncomputable def conjDescentForm : BilinForm h.fixedField (conjFixed h τ) :=
  LinearMap.mk₂ h.fixedField
    (fun v w => ⟨c * Hf v w, h.mem_fixedField.mpr (hc v w v.2 w.2)⟩)
    (fun v₁ v₂ w => Subtype.ext (by
      simp only [Submodule.coe_add, map_add, LinearMap.add_apply, mul_add, Subfield.coe_add]))
    (fun k v w => Subtype.ext (by
      simp only [Submodule.coe_smul, Subfield.smul_def, map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, Subfield.coe_mul, h.mem_fixedField.mp k.2]
      ring))
    (fun v w₁ w₂ => Subtype.ext (by
      simp only [Submodule.coe_add, map_add, mul_add, Subfield.coe_add]))
    (fun k v w => Subtype.ext (by
      simp only [Submodule.coe_smul, Subfield.smul_def, map_smul, smul_eq_mul, Subfield.coe_mul]
      ring))

theorem conjDescentForm_apply (v w : conjFixed h τ) :
    (conjDescentForm Hf τ c hc v w : E) = c * Hf v w :=
  rfl

end Form

section Nondeg

variable {Hf : V →ₛₗ[h.bar] V →ₗ[E] E} (hH : Hf.IsSymm) (hnd : Hf.SeparatingLeft)
  {τ : V →ₛₗ[h.bar] V}

include hnd in
theorem eq_zero_of_forall_conjFixed (hspan : Submodule.span E (conjFixed h τ : Set V) = ⊤)
    {v : V} (hv : ∀ w ∈ conjFixed h τ, Hf v w = 0) : v = 0 := by
  refine hnd v fun u => ?_
  have hu : u ∈ Submodule.span E (conjFixed h τ : Set V) := hspan ▸ Submodule.mem_top
  induction hu using Submodule.span_induction with
  | mem x hx => exact hv x hx
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_smul, hx, smul_zero]

include hH hnd in
theorem conjDescentForm_nondegenerate (hspan : Submodule.span E (conjFixed h τ : Set V) = ⊤)
    {c : E} (hc0 : c ≠ 0)
    (hc : ∀ v w, v ∈ conjFixed h τ → w ∈ conjFixed h τ → h.bar (c * Hf v w) = c * Hf v w) :
    (conjDescentForm Hf τ c hc).Nondegenerate := by
  refine ⟨fun v hv => Subtype.ext (eq_zero_of_forall_conjFixed hnd hspan fun w hw => ?_),
    fun v hv => Subtype.ext (eq_zero_of_forall_conjFixed hnd hspan fun w hw => ?_)⟩
  · have h1 := congrArg Subtype.val (hv ⟨w, hw⟩)
    rw [conjDescentForm_apply, ZeroMemClass.coe_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_left hc0
  · have h1 := congrArg Subtype.val (hv ⟨w, hw⟩)
    rw [conjDescentForm_apply, ZeroMemClass.coe_zero] at h1
    rw [← hH.eq w v, (mul_eq_zero.mp h1).resolve_left hc0, map_zero]

end Nondeg

@[expose] def commutingUnitary (Hf : V →ₛₗ[h.bar] V →ₗ[E] E) (τ₀ : V →ₛₗ[h.bar] V) :
    Subgroup (LinearMap.GeneralLinearGroup E V) where
  carrier := {g | g ∈ sesqUnitaryGroup Hf ∧
    ∀ v, (g : V →ₗ[E] V) (τ₀ v) = τ₀ ((g : V →ₗ[E] V) v)}
  one_mem' := ⟨one_mem _, fun _ => rfl⟩
  mul_mem' {g g'} hg hg' := ⟨mul_mem hg.1 hg'.1, fun v => by
    change (g : V →ₗ[E] V) ((g' : V →ₗ[E] V) (τ₀ v)) =
      τ₀ ((g : V →ₗ[E] V) ((g' : V →ₗ[E] V) v))
    rw [hg'.2, hg.2]⟩
  inv_mem' {g} hg := ⟨inv_mem hg.1, fun v => by
    have h1 : ∀ x, (g : V →ₗ[E] V) (((g⁻¹ : LinearMap.GeneralLinearGroup E V) :
        V →ₗ[E] V) x) = x := fun x => by
      rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Module.End.one_apply]
    have h2 : ∀ x, ((g⁻¹ : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V)
        ((g : V →ₗ[E] V) x) = x := fun x => by
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply]
    calc ((g⁻¹ : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) (τ₀ v)
        = ((g⁻¹ : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V)
            (τ₀ ((g : V →ₗ[E] V) (((g⁻¹ : LinearMap.GeneralLinearGroup E V) :
              V →ₗ[E] V) v))) := by rw [h1]
      _ = ((g⁻¹ : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V)
            ((g : V →ₗ[E] V) (τ₀ (((g⁻¹ : LinearMap.GeneralLinearGroup E V) :
              V →ₗ[E] V) v))) := by rw [hg.2]
      _ = τ₀ (((g⁻¹ : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) v) := h2 _⟩

theorem mem_commutingUnitary {Hf : V →ₛₗ[h.bar] V →ₗ[E] E} {τ₀ : V →ₛₗ[h.bar] V}
    {g : LinearMap.GeneralLinearGroup E V} :
    g ∈ commutingUnitary Hf τ₀ ↔ g ∈ sesqUnitaryGroup Hf ∧
      ∀ v, (g : V →ₗ[E] V) (τ₀ v) = τ₀ ((g : V →ₗ[E] V) v) :=
  Iff.rfl

theorem map_mem_conjFixed {τ₀ : V →ₛₗ[h.bar] V} {g : V →ₗ[E] V} (hg : ∀ v, g (τ₀ v) = τ₀ (g v))
    (b : E) {w : V} (hw : w ∈ conjFixed h (b • τ₀)) : g w ∈ conjFixed h (b • τ₀) := by
  rw [mem_conjFixed, LinearMap.smul_apply] at hw ⊢
  rw [← hg, ← map_smul, hw]

section Restrict

variable {Hf : V →ₛₗ[h.bar] V →ₗ[E] E} {τ₀ : V →ₛₗ[h.bar] V} {b : E}

theorem coe_commutingUnitary_mul_inv (g : commutingUnitary Hf τ₀) (x : V) :
    (((g : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V))
      ((((g⁻¹ : commutingUnitary Hf τ₀) : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) x) =
        x := by
  rw [← Module.End.mul_apply, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
    Subgroup.coe_one, Units.val_one, Module.End.one_apply]

theorem coe_commutingUnitary_inv_mul (g : commutingUnitary Hf τ₀) (x : V) :
    ((((g⁻¹ : commutingUnitary Hf τ₀) : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V))
      (((g : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) x) = x := by
  rw [← Module.End.mul_apply, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel,
    Subgroup.coe_one, Units.val_one, Module.End.one_apply]

variable (b) in
@[expose] noncomputable def restrictConjFixed (g : commutingUnitary Hf τ₀) :
    conjFixed h (b • τ₀) ≃ₗ[h.fixedField] conjFixed h (b • τ₀) :=
  LinearEquiv.ofLinearMap
    ((((g : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V).restrictScalars h.fixedField).restrict
      fun _ hw => map_mem_conjFixed g.2.2 b hw)
    (((((g⁻¹ : commutingUnitary Hf τ₀) : LinearMap.GeneralLinearGroup E V) :
      V →ₗ[E] V).restrictScalars h.fixedField).restrict
        fun _ hw => map_mem_conjFixed (g⁻¹).2.2 b hw)
    (LinearMap.ext fun w => Subtype.ext (coe_commutingUnitary_mul_inv g w))
    (LinearMap.ext fun w => Subtype.ext (coe_commutingUnitary_inv_mul g w))

theorem coe_restrictConjFixed (g : commutingUnitary Hf τ₀) (w : conjFixed h (b • τ₀)) :
    (restrictConjFixed b g w : V) = ((g : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) w :=
  rfl

variable (b) in
@[expose] noncomputable def restrictConjFixedHom :
    commutingUnitary Hf τ₀ →* (conjFixed h (b • τ₀) ≃ₗ[h.fixedField] conjFixed h (b • τ₀)) where
  toFun := restrictConjFixed b
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

end Restrict

section Equiv

variable {Hf : V →ₛₗ[h.bar] V →ₗ[E] E} {τ₀ : V →ₛₗ[h.bar] V} {b : E}

theorem exists_restrict_equiv [FiniteDimensional E V] (hττ : ∀ v, (b • τ₀) ((b • τ₀) v) = v)
    (hb0 : b ≠ 0) {t : E} (ht : h.bar t = -t) (ht0 : t ≠ 0) (h2 : (2 : E) ≠ 0) {c : E}
    (hc0 : c ≠ 0) (hc : ∀ v w, v ∈ conjFixed h (b • τ₀) → w ∈ conjFixed h (b • τ₀) →
      h.bar (c * Hf v w) = c * Hf v w) :
    ∃ Φ : commutingUnitary Hf τ₀ ≃*
        TauCeti.BilinForm.isometryGroup (conjDescentForm Hf (b • τ₀) c hc),
      ∀ g w, (((Φ g : conjFixed h (b • τ₀) ≃ₗ[h.fixedField] conjFixed h (b • τ₀)) w :
        conjFixed h (b • τ₀)) : V) = ((g : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) w := by
  have hspan := span_conjFixed hττ ht ht0 h2
  have hmemB : ∀ g : commutingUnitary Hf τ₀, restrictConjFixedHom b g ∈
      TauCeti.BilinForm.isometryGroup (conjDescentForm Hf (b • τ₀) c hc) := by
    intro g
    rw [TauCeti.BilinForm.mem_isometryGroup_iff]
    intro x y
    apply Subtype.ext
    rw [conjDescentForm_apply, conjDescentForm_apply]
    change c * Hf (((g : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) x)
      (((g : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) y) = _
    rw [(mem_sesqUnitaryGroup.mp g.2.1) x y]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : commutingUnitary Hf τ₀ →*
      TauCeti.BilinForm.isometryGroup (conjDescentForm Hf (b • τ₀) c hc),
        ∀ g, (ψ g : conjFixed h (b • τ₀) ≃ₗ[h.fixedField] conjFixed h (b • τ₀)) =
          restrictConjFixedHom b g :=
    ⟨(restrictConjFixedHom b).codRestrict _ hmemB, fun _ => rfl⟩
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    refine Subtype.ext (Units.ext (LinearMap.ext_on hspan fun w hw => ?_))
    have h1 := congrArg (fun φ : TauCeti.BilinForm.isometryGroup
      (conjDescentForm Hf (b • τ₀) c hc) =>
        (((φ : conjFixed h (b • τ₀) ≃ₗ[h.fixedField] conjFixed h (b • τ₀)) ⟨w, hw⟩ :
          conjFixed h (b • τ₀)) : V)) hg
    simp only [hψ] at h1
    exact h1
  have hsurj : Function.Surjective ψ := by
    rintro ⟨φ, hφ⟩
    obtain ⟨Θ, hΘ⟩ : ∃ Θ : TensorProduct h.fixedField E (conjFixed h (b • τ₀)) ≃ₗ[E] V,
        ∀ (a : E) (w : conjFixed h (b • τ₀)), Θ (a ⊗ₜ w) = a • (w : V) :=
      ⟨LinearEquiv.ofBijective _ (liftBaseChange_conjFixed_bijective hττ ht ht0 h2),
        fun a w => LinearMap.liftBaseChange_tmul E _ a w⟩
    obtain ⟨g', hg'⟩ : ∃ g' : V ≃ₗ[E] V,
        g' = Θ.symm.trans ((LinearEquiv.baseChange h.fixedField E _ _ φ).trans Θ) := ⟨_, rfl⟩
    have hg'W : ∀ w : conjFixed h (b • τ₀), g' w = φ w := by
      intro w
      have h1 : Θ.symm (w : V) = 1 ⊗ₜ w := by rw [Θ.symm_apply_eq, hΘ, one_smul]
      rw [hg', LinearEquiv.trans_apply, LinearEquiv.trans_apply, h1,
        LinearEquiv.baseChange_tmul, hΘ, one_smul]
    have hτW : ∀ w ∈ conjFixed h (b • τ₀), τ₀ w = b⁻¹ • w := by
      intro w hw
      have h1 := mem_conjFixed.mp hw
      rw [LinearMap.smul_apply] at h1
      conv_rhs => rw [← h1]
      rw [smul_smul, inv_mul_cancel₀ hb0, one_smul]
    have hg'τ : ∀ v, g' (τ₀ v) = τ₀ (g' v) := by
      intro v
      have hv : v ∈ Submodule.span E (conjFixed h (b • τ₀) : Set V) := hspan ▸ Submodule.mem_top
      induction hv using Submodule.span_induction with
      | mem x hx =>
        rw [hτW x hx, g'.map_smul, show g' x = φ ⟨x, hx⟩ from hg'W ⟨x, hx⟩,
          hτW _ (φ ⟨x, hx⟩).2]
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
      | smul a x _ hx =>
        rw [τ₀.map_smulₛₗ a x, g'.map_smul (h.bar a) (τ₀ x), hx, g'.map_smul a x,
          τ₀.map_smulₛₗ a (g' x)]
    have hφB : ∀ x y : conjFixed h (b • τ₀), Hf (φ x) (φ y) = Hf x y := by
      intro x y
      have h1 := congrArg Subtype.val ((TauCeti.BilinForm.mem_isometryGroup_iff.mp hφ) x y)
      rw [conjDescentForm_apply, conjDescentForm_apply] at h1
      exact mul_left_cancel₀ hc0 h1
    have hg'H1 : ∀ (x : V) (y : conjFixed h (b • τ₀)), Hf (g' x) (g' y) = Hf x y := by
      intro x y
      have hx : x ∈ Submodule.span E (conjFixed h (b • τ₀) : Set V) := hspan ▸ Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem z hz =>
        rw [show g' z = φ ⟨z, hz⟩ from hg'W ⟨z, hz⟩, hg'W y]
        exact hφB ⟨z, hz⟩ y
      | zero => simp
      | add z z' _ _ hz hz' =>
        rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hz, hz']
      | smul a z _ hz =>
        rw [g'.map_smul a z, Hf.map_smulₛₗ a (g' z), Hf.map_smulₛₗ a z, LinearMap.smul_apply,
          LinearMap.smul_apply, hz]
    have hg'H : ∀ x y : V, Hf (g' x) (g' y) = Hf x y := by
      intro x y
      have hy : y ∈ Submodule.span E (conjFixed h (b • τ₀) : Set V) := hspan ▸ Submodule.mem_top
      induction hy using Submodule.span_induction with
      | mem z hz => exact hg'H1 x ⟨z, hz⟩
      | zero => simp
      | add z z' _ _ hz hz' => rw [map_add, map_add, map_add, hz, hz']
      | smul a z _ hz => rw [g'.map_smul a z, map_smul, map_smul, hz]
    obtain ⟨gU, hgU⟩ : ∃ gU : LinearMap.GeneralLinearGroup E V,
        (gU : V →ₗ[E] V) = g'.toLinearMap :=
      ⟨⟨g'.toLinearMap, g'.symm.toLinearMap, LinearMap.ext fun x => g'.apply_symm_apply x,
        LinearMap.ext fun x => g'.symm_apply_apply x⟩, rfl⟩
    have hgUmem : gU ∈ commutingUnitary Hf τ₀ :=
      ⟨mem_sesqUnitaryGroup.mpr fun x y => by rw [hgU]; exact hg'H x y,
        fun v => by rw [hgU]; exact hg'τ v⟩
    refine ⟨⟨gU, hgUmem⟩, Subtype.ext ?_⟩
    rw [hψ]
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    change (gU : V →ₗ[E] V) w = (φ w : V)
    rw [hgU]
    exact hg'W w
  refine ⟨MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩, fun g w => ?_⟩
  change ((ψ g : conjFixed h (b • τ₀) ≃ₗ[h.fixedField] conjFixed h (b • τ₀)) w : V) = _
  rw [hψ]
  rfl

end Equiv

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
