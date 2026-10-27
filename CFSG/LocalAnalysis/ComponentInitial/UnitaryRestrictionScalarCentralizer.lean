module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRestrictionCentralizer

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Module

variable {p f : ℕ} {E : Type} [Field E] {h : UnitaryFieldData p f E}
  {V : Type} [AddCommGroup V] [Module E V]

section TraceForm

variable (Hf : V →ₛₗ[h.bar] V →ₗ[E] E) (s : E)

@[expose] noncomputable def traceForm : LinearMap.BilinForm h.fixedField V :=
  LinearMap.mk₂ h.fixedField
    (fun v w => ⟨s * Hf v w + h.bar (s * Hf v w),
      by rw [h.mem_fixedField, map_add, h.bar_bar, add_comm]⟩)
    (fun v₁ v₂ w => Subtype.ext (by
      simp only [map_add, LinearMap.add_apply, mul_add, Subfield.coe_add]
      ring))
    (fun c v w => Subtype.ext (by
      simp only [Subfield.smul_def, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        Subfield.coe_mul, map_mul, h.mem_fixedField.mp c.2]
      ring))
    (fun v w₁ w₂ => Subtype.ext (by
      simp only [map_add, mul_add, Subfield.coe_add]
      ring))
    (fun c v w => Subtype.ext (by
      simp only [Subfield.smul_def, map_smul, smul_eq_mul, Subfield.coe_mul, map_mul,
        h.mem_fixedField.mp c.2]
      ring))

theorem traceForm_apply (v w : V) :
    (traceForm Hf s v w : E) = s * Hf v w + h.bar (s * Hf v w) :=
  rfl

variable {Hf s}

theorem traceForm_isAlt (hH : Hf.IsSymm) (hs : h.bar s = -s) : (traceForm Hf s).IsAlt := by
  intro v
  apply Subtype.ext
  have hvv : h.bar (Hf v v) = Hf v v := hH.eq v v
  rw [traceForm_apply, map_mul, hs, hvv, ZeroMemClass.coe_zero]
  ring

theorem traceForm_eq_two {v w : V} (hvw : s * Hf v w = 1) : (traceForm Hf s v w : E) = 2 := by
  rw [traceForm_apply, hvw, map_one]
  norm_num

theorem traceForm_nondegenerate (hnd : Hf.Nondegenerate) (hs0 : s ≠ 0) (h2 : (2 : E) ≠ 0) :
    (traceForm Hf s).Nondegenerate := by
  refine ⟨fun v hv => ?_, fun w hw => ?_⟩
  · by_contra hv0
    obtain ⟨w₀, hw₀⟩ : ∃ w₀, Hf v w₀ ≠ 0 := by
      by_contra! h0
      exact hv0 (hnd.1 v h0)
    have h1 := traceForm_eq_two (Hf := Hf) (s := s) (v := v) (w := (s * Hf v w₀)⁻¹ • w₀)
      (by rw [map_smul, smul_eq_mul, ← mul_assoc, mul_comm s, mul_assoc,
        inv_mul_cancel₀ (mul_ne_zero hs0 hw₀)])
    rw [hv, ZeroMemClass.coe_zero] at h1
    exact h2 h1.symm
  · by_contra hw0
    obtain ⟨v₀, hv₀⟩ : ∃ v₀, Hf v₀ w ≠ 0 := by
      by_contra! h0
      exact hw0 (hnd.2 w h0)
    have h1 := traceForm_eq_two (Hf := Hf) (s := s) (v := h.bar (s * Hf v₀ w)⁻¹ • v₀) (w := w)
      (by rw [LinearMap.map_smulₛₗ₂, h.bar_bar, smul_eq_mul, ← mul_assoc, mul_comm s,
        mul_assoc, inv_mul_cancel₀ (mul_ne_zero hs0 hv₀)])
    rw [hw, ZeroMemClass.coe_zero] at h1
    exact h2 h1.symm

theorem traceForm_inv {g : LinearMap.GeneralLinearGroup E V} (hg : g ∈ sesqSpecialUnitaryGroup Hf)
    (u v : V) : traceForm Hf s ((g : V →ₗ[E] V) u) ((g : V →ₗ[E] V) v) = traceForm Hf s u v := by
  apply Subtype.ext
  rw [traceForm_apply, traceForm_apply, (sesqSpecialUnitaryGroup_le Hf hg) u v]

end TraceForm


theorem natural_odd_unitary_restriction_scalar_centralizer (h : UnitaryFieldData p f E)
    (hp : p ≠ 2) [FiniteDimensional E V] (hm : 3 ≤ finrank E V)
    {Hf : V →ₛₗ[h.bar] V →ₗ[E] E} (hH : Hf.IsSymm) (hnd : Hf.Nondegenerate) :
    (∀ X : LinearMap.GeneralLinearGroup h.fixedField V,
      X ∈ Subgroup.centralizer (((sesqSpecialUnitaryGroup Hf).map
        (glRestrictScalars h.fixedField)) : Set (LinearMap.GeneralLinearGroup h.fixedField V)) ↔
        ∃ a : Eˣ, ∀ v, (X : V →ₗ[h.fixedField] V) v = (a : E) • v) ∧
      ∀ X ∈ Subgroup.centralizer (((sesqSpecialUnitaryGroup Hf).map
          (glRestrictScalars h.fixedField)) : Set (LinearMap.GeneralLinearGroup h.fixedField V)),
        ∀ Y ∈ Subgroup.centralizer (((sesqSpecialUnitaryGroup Hf).map
          (glRestrictScalars h.fixedField)) : Set (LinearMap.GeneralLinearGroup h.fixedField V)),
          X * Y = Y * X := by
  have h2 : (2 : E) ≠ 0 := by
    have : CharP E p := h.charP
    intro h0
    have h3 : ((2 : ℕ) : E) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff E p] at h3
    exact hp ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp h3)
  obtain ⟨z, hz⟩ := h.exists_bar_ne
  have hs0 : z - h.bar z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hs : h.bar (z - h.bar z) = -(z - h.bar z) := by rw [map_sub, h.bar_bar, neg_sub]
  exact (unitary_restriction_symplectic_centralizer_solvable h hp (by omega) hH hnd
    (traceForm Hf (z - h.bar z)) (traceForm_nondegenerate hnd hs0 h2)
    (traceForm_isAlt hH hs) fun g hg u v => traceForm_inv hg u v).2 hm

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
