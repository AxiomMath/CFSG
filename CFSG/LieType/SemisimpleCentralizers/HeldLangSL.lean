module

public import CFSG.LieType.SemisimpleCentralizers.HeldLang
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open Matrix CFSG.HardMathSupport.Foote.ModuleExclusions

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def twistHom (H : Subgroup (GL ι F)) (σ : F ≃+* F) (g : GL ι F)
    (hH : ∀ x ∈ H, g * glMap σ x * g⁻¹ ∈ H) : H →* H where
  toFun x := ⟨g * glMap σ x * g⁻¹, hH x x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul, map_mul]; group)

theorem coe_twistHom (H : Subgroup (GL ι F)) (σ : F ≃+* F) (g : GL ι F)
    (hH : ∀ x ∈ H, g * glMap σ x * g⁻¹ ∈ H) (x : H) :
    ((twistHom H σ g hH x : H) : GL ι F) = g * glMap σ x * g⁻¹ := rfl

theorem glMap_pow_succ (σ : F ≃+* F) (k : ℕ) (x : GL ι F) :
    glMap (σ ^ (k + 1)) x = glMap σ (glMap (σ ^ k) x) := by
  apply Units.ext
  ext i j
  simp only [coe_glMap, Matrix.map_apply, pow_succ', RingAut.mul_apply]

theorem glMap_one (x : GL ι F) : glMap (1 : F ≃+* F) x = x := by
  apply Units.ext
  ext i j
  simp [coe_glMap]

theorem glMap_pow_zero (σ : F ≃+* F) (x : GL ι F) : glMap (σ ^ 0) x = x := by
  rw [pow_zero, glMap_one]

theorem coe_iterate_twistHom (H : Subgroup (GL ι F)) (σ : F ≃+* F) (g : GL ι F)
    (hH : ∀ x ∈ H, g * glMap σ x * g⁻¹ ∈ H) (k : ℕ) (x : H) :
    (((twistHom H σ g hH)^[k] x : H) : GL ι F) =
      normProd σ g k * glMap (σ ^ k) x * (normProd σ g k)⁻¹ := by
  induction k with
  | zero => simp [normProd, glMap_one]
  | succ k ih =>
    rw [Function.iterate_succ_apply', coe_twistHom, ih, glMap_pow_succ]
    simp only [normProd, map_mul, map_inv]
    group

theorem iterate_twist_formula (σ : F ≃+* F) (g : GL ι F) (k : ℕ) (y : GL ι F) :
    (fun z : GL ι F => g * glMap σ z * g⁻¹)^[k] y =
      normProd σ g k * glMap (σ ^ k) y * (normProd σ g k)⁻¹ := by
  induction k with
  | zero => simp [normProd, glMap_one]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, glMap_pow_succ]
    simp only [normProd, map_mul, map_inv]
    group

theorem mem_fixHom_twistHom_iff (H : Subgroup (GL ι F)) (σ : F ≃+* F) (g y : GL ι F)
    (hH : ∀ x ∈ H, g * glMap σ x * g⁻¹ ∈ H)
    (hy : ∀ x : GL ι F, g * glMap σ x * g⁻¹ = y⁻¹ * glMap σ (y * x * y⁻¹) * y) (x : H) :
    x ∈ fixHom (twistHom H σ g hH) ↔ y * (x : GL ι F) * y⁻¹ ∈ glFix σ := by
  rw [mem_fixHom, Subtype.ext_iff, coe_twistHom, hy, mem_glFix]
  constructor
  · intro h
    have : glMap σ (y * (x : GL ι F) * y⁻¹) = y * (y⁻¹ * glMap σ (y * (x : GL ι F) * y⁻¹) * y) * y⁻¹ := by
      group
    rw [this, h]
  · intro h
    rw [h]
    group

abbrev slGL (ι : Type*) [Fintype ι] [DecidableEq ι] (F : Type*) [Field F] : Subgroup (GL ι F) :=
  (Matrix.GeneralLinearGroup.det : GL ι F →* Fˣ).ker

theorem mem_slGL {x : GL ι F} : x ∈ slGL ι F ↔ (x : Matrix ι ι F).det = 1 := by
  rw [MonoidHom.mem_ker, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply]
  rfl

theorem det_glMap (σ : F ≃+* F) (x : GL ι F) :
    ((glMap σ x : GL ι F) : Matrix ι ι F).det = σ (x : Matrix ι ι F).det := by
  rw [coe_glMap]
  exact (RingHom.map_det (σ : F →+* F) (x : Matrix ι ι F)).symm

theorem slTwist_mem (σ : F ≃+* F) (g : GL ι F) {x : GL ι F} (hx : x ∈ slGL ι F) :
    g * glMap σ x * g⁻¹ ∈ slGL ι F := by
  rw [mem_slGL] at hx ⊢
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, det_glMap, hx, map_one, mul_one,
    ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

theorem conj_mem_slGL (y : GL ι F) {x : GL ι F} (hx : x ∈ slGL ι F) : y * x * y⁻¹ ∈ slGL ι F := by
  rw [mem_slGL] at hx ⊢
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hx, mul_one, ← Matrix.det_mul,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

@[expose] def slTwist (σ : F ≃+* F) (g : GL ι F) : slGL ι F →* slGL ι F :=
  twistHom (slGL ι F) σ g fun _ hx => slTwist_mem σ g hx

theorem coe_slTwist (σ : F ≃+* F) (g : GL ι F) (x : slGL ι F) :
    ((slTwist σ g x : slGL ι F) : GL ι F) = g * glMap σ x * g⁻¹ := rfl

theorem mem_slGL_inf_glFix_iff (σ : F ≃+* F) {w : GL ι F} :
    w ∈ slGL ι F ⊓ glFix σ ↔ ∃ x₀ : slGL ι (fixField σ), glFixEmb σ x₀ = w := by
  constructor
  · intro hw
    obtain ⟨hs, hf⟩ := Subgroup.mem_inf.1 hw
    obtain ⟨x₀, hx₀⟩ : w ∈ (glFixEmb (ι := ι) σ).range := by rwa [glFixEmb_range]
    refine ⟨⟨x₀, ?_⟩, hx₀⟩
    rw [mem_slGL] at hs ⊢
    have h1 : ((glFixEmb σ x₀ : GL ι F) : Matrix ι ι F) = (x₀ : Matrix ι ι (fixField σ)).map (fixField σ).subtype := by
      ext i j
      rw [glFixEmb_apply]
      rfl
    rw [← hx₀, h1, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hs
    exact (fixField σ).subtype_injective (by simpa using hs)
  · rintro ⟨x₀, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, glFixEmb_mem σ (x₀ : GL ι (fixField σ))⟩
    have hs := x₀.2
    rw [mem_slGL] at hs ⊢
    have h1 : ((glFixEmb σ (x₀ : GL ι (fixField σ)) : GL ι F) : Matrix ι ι F) =
        ((x₀ : GL ι (fixField σ)) : Matrix ι ι (fixField σ)).map (fixField σ).subtype := by
      ext i j
      rw [glFixEmb_apply]
      rfl
    rw [h1, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hs]
    simp

theorem exists_slTwist_fix [Finite F] [Nonempty ι] (σ : F ≃+* F) (g : GL ι F) (c : F)
    (hg : Ai σ (g : Matrix ι ι F) (orderOf σ) = c • (1 : Matrix ι ι F)) :
    ∃ y : GL ι F,
      (∀ x : slGL ι F, ((slTwist σ g x : slGL ι F) : GL ι F) = y⁻¹ * glMap σ (y * (x : GL ι F) * y⁻¹) * y) ∧
      ∀ x : slGL ι F, x ∈ fixHom (slTwist σ g) ↔
        ∃ x₀ : slGL ι (fixField σ), (x : GL ι F) = y⁻¹ * glFixEmb σ x₀ * y := by
  obtain ⟨y, hy⟩ := exists_twist_eq_conj σ g c hg
  refine ⟨y, fun x => hy x, fun x => ?_⟩
  refine (mem_fixHom_twistHom_iff (slGL ι F) σ g y (fun _ hx => slTwist_mem σ g hx) hy x).trans ?_
  have hyx : y * (x : GL ι F) * y⁻¹ ∈ slGL ι F := by
    have := x.2
    rw [mem_slGL] at this ⊢
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, this, mul_one,
      ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  constructor
  · intro h
    obtain ⟨x₀, hx₀⟩ := (mem_slGL_inf_glFix_iff σ).1 ⟨hyx, h⟩
    refine ⟨x₀, ?_⟩
    rw [hx₀]
    group
  · rintro ⟨x₀, hx₀⟩
    have : y * (x : GL ι F) * y⁻¹ = glFixEmb σ x₀ := by
      rw [hx₀]
      group
    rw [this]
    exact ((mem_slGL_inf_glFix_iff σ).2 ⟨x₀, rfl⟩).2

theorem exists_scalar_of_commute_slGL (g : GL ι F) (h : ∀ x ∈ slGL ι F, g * x * g⁻¹ = x) :
    ∃ c : Fˣ, g = Matrix.GeneralLinearGroup.scalar ι c := by
  have hcomm : ∀ x ∈ slGL ι F, x * g = g * x := fun x hx => by
    have := h x hx
    calc x * g = g * x * g⁻¹ * g := by rw [this]
      _ = g * x := by group
  have hscal : (g : Matrix ι ι F) ∈ Set.range (Matrix.scalar ι) := by
    refine Matrix.mem_range_scalar_of_commute_transvectionStruct fun t => ?_
    let T : GL ι F := ⟨t.toMatrix, t.inv.toMatrix, t.mul_inv, t.inv_mul⟩
    have hT : T ∈ slGL ι F := mem_slGL.2 t.det
    exact congrArg (fun z : GL ι F => (z : Matrix ι ι F)) (hcomm T hT)
  have hg : g ∈ Subgroup.center (GL ι F) :=
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2 hscal
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
  obtain ⟨c, hc⟩ := hg
  exact ⟨c, hc.symm⟩

theorem coe_iterate_slTwist (σ : F ≃+* F) (g : GL ι F) (k : ℕ) (x : slGL ι F) :
    (((slTwist σ g)^[k] x : slGL ι F) : GL ι F) =
      normProd σ g k * glMap (σ ^ k) x * (normProd σ g k)⁻¹ :=
  coe_iterate_twistHom (slGL ι F) σ g _ k x

theorem exists_scalar_normProd [Finite F] (σ : F ≃+* F) (g : GL ι F)
    (h : ∀ x : slGL ι F, (slTwist σ g)^[orderOf σ] x = x) :
    ∃ c : F, Ai σ (g : Matrix ι ι F) (orderOf σ) = c • (1 : Matrix ι ι F) := by
  obtain ⟨c, hc⟩ := exists_scalar_of_commute_slGL (normProd σ g (orderOf σ)) fun x hx => by
    have := congrArg (fun z : slGL ι F => (z : GL ι F)) (h ⟨x, hx⟩)
    simpa [coe_iterate_slTwist, pow_orderOf_eq_one, glMap_one] using this
  refine ⟨c, ?_⟩
  rw [← coe_normProd, hc, Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]

theorem iterate_slTwist_orderOf [Finite F] (σ : F ≃+* F) (g : GL ι F) (c : Fˣ)
    (h : normProd σ g (orderOf σ) = Matrix.GeneralLinearGroup.scalar ι c) (x : slGL ι F) :
    (slTwist σ g)^[orderOf σ] x = x := by
  apply Subtype.ext
  rw [coe_iterate_slTwist, pow_orderOf_eq_one, glMap_one, h, scalar_mul_comm, mul_assoc,
    mul_inv_cancel, mul_one]

abbrev slScalars (ι : Type*) [Fintype ι] [DecidableEq ι] (F : Type*) [Field F] : Subgroup (slGL ι F) :=
  (Subgroup.center (GL ι F)).subgroupOf (slGL ι F)

theorem slScalars_le_center : slScalars ι F ≤ Subgroup.center (slGL ι F) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (Subgroup.mem_center_iff.1 (Subgroup.mem_subgroupOf.1 hx) y)

abbrev PSL (ι : Type*) [Fintype ι] [DecidableEq ι] (F : Type*) [Field F] : Type _ :=
  slGL ι F ⧸ slScalars ι F

theorem glMap_mem_center (σ : F ≃+* F) {x : GL ι F} (hx : x ∈ Subgroup.center (GL ι F)) :
    glMap σ x ∈ Subgroup.center (GL ι F) := by
  rw [Subgroup.mem_center_iff] at hx ⊢
  intro w
  have hw : glMap σ (glMap σ.symm w) = w := by
    apply Units.ext
    ext i j
    simp [coe_glMap]
  rw [← hw, ← map_mul, ← map_mul, hx]

theorem slTwist_scalars_mem (σ : F ≃+* F) (g : GL ι F) {x : slGL ι F} (hx : x ∈ slScalars ι F) :
    slTwist σ g x ∈ slScalars ι F := by
  have hx' : (x : GL ι F) ∈ Subgroup.center (GL ι F) := Subgroup.mem_subgroupOf.1 hx
  rw [Subgroup.mem_subgroupOf, coe_slTwist]
  have h1 := glMap_mem_center σ hx'
  rw [Subgroup.mem_center_iff] at h1 ⊢
  intro w
  have h2 := h1 (g⁻¹ * w * g)
  calc w * (g * glMap σ x * g⁻¹) = g * (g⁻¹ * w * g * glMap σ x) * g⁻¹ := by group
    _ = g * (glMap σ x * (g⁻¹ * w * g)) * g⁻¹ := by rw [h2]
    _ = g * glMap σ x * g⁻¹ * w := by group

@[expose] def slTwistBar (σ : F ≃+* F) (g : GL ι F) : PSL ι F →* PSL ι F :=
  QuotientGroup.map (slScalars ι F) (slScalars ι F) (slTwist σ g)
    fun _ hx => slTwist_scalars_mem σ g hx

theorem slTwistBar_mk (σ : F ≃+* F) (g : GL ι F) (x : slGL ι F) :
    slTwistBar σ g (x : PSL ι F) = ((slTwist σ g x : slGL ι F) : PSL ι F) :=
  QuotientGroup.map_mk _ _ _ _ x

theorem exists_psl_fix [Finite F] [Nonempty ι] (σ : F ≃+* F) (g : GL ι F) (c : F)
    (hg : Ai σ (g : Matrix ι ι F) (orderOf σ) = c • (1 : Matrix ι ι F)) :
    ∃ y : GL ι F,
      (∀ x : slGL ι F, x ∈ fixHom (slTwist σ g) ↔
        ∃ x₀ : slGL ι (fixField σ), (x : GL ι F) = y⁻¹ * glFixEmb σ x₀ * y) ∧
      (fixHom (slTwist σ g)).map (QuotientGroup.mk' (slScalars ι F)) ≤ fixHom (slTwistBar σ g) ∧
      (((fixHom (slTwist σ g)).map (QuotientGroup.mk' (slScalars ι F))).subgroupOf
        (fixHom (slTwistBar σ g))).Normal ∧
      ⁅fixHom (slTwistBar σ g), fixHom (slTwistBar σ g)⁆ ≤
        (fixHom (slTwist σ g)).map (QuotientGroup.mk' (slScalars ι F)) := by
  obtain ⟨y, -, hy⟩ := exists_slTwist_fix σ g c hg
  refine ⟨y, hy, ?_, ?_, ?_⟩
  · have hβ' := slTwistBar_mk (ι := ι) σ g
    rw [fix_quot_eq_map (slTwist σ g) slScalars_le_center (slTwistBar σ g) hβ']
    exact Subgroup.map_mono (fixHom_le_twistedFix _ _ _)
  · exact map_fixHom_normal (slTwist σ g) slScalars_le_center _ (slTwistBar_mk (ι := ι) σ g)
  · exact commutator_fixHom_le (slTwist σ g) slScalars_le_center _ (slTwistBar_mk (ι := ι) σ g)

theorem le_map_fix_of_perfect_psl (σ : F ≃+* F) (g : GL ι F) {J : Subgroup (PSL ι F)}
    (hJ : ⁅J, J⁆ = J) (hJf : J ≤ fixHom (slTwistBar σ g)) :
    J ≤ (fixHom (slTwist σ g)).map (QuotientGroup.mk' (slScalars ι F)) :=
  le_map_fixHom_of_perfect (slTwist σ g) slScalars_le_center _ (slTwistBar_mk σ g) hJ hJf

end CFSG.LieType.SemisimpleCentralizers.HeldLang
