module

public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsOrthLow

public section

namespace CFSG.GroupTheory

section QuadraticPlane

open QuadraticMap TauCeti.QuadraticMap CFSG.ClassicalInvolution.Q3

variable {F W : Type*} [Field F] [AddCommGroup W] [Module F W] {Q : QuadraticForm F W}

theorem isometry_commute_or_inv_of_det_eq_one (h2 : (2 : F) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : Module.finrank F W = 2)
    {s : W ≃ₗ[F] W} (hs : s ∈ orthogonalGroup Q) :
    (∀ r : W ≃ₗ[F] W, r ∈ orthogonalGroup Q → LinearEquiv.det r = 1 → s * r = r * s) ∨
    (∀ r : W ≃ₗ[F] W, r ∈ orthogonalGroup Q → LinearEquiv.det r = 1 →
      s * r * s⁻¹ = r⁻¹) := by
  haveI : FiniteDimensional F W := .of_finrank_pos (by rw [hdim]; norm_num)
  obtain ⟨l, -, -, -, hdet⟩ := exists_det_eq_neg_one_pow h2 hQ hs
  rcases Nat.even_or_odd l.length with he | ho
  · left
    intro r hr hdr
    have hds : LinearEquiv.det s = 1 := by rw [hdet, he.neg_one_pow]
    exact commute_of_det_eq_one_of_finrank_le_two h2 hQ hdim.le hs hr hds hdr
  · right
    have hds : LinearEquiv.det s = -1 := by rw [hdet, ho.neg_one_pow]
    have hss : s * s = 1 := mul_self_eq_one_of_det_eq_neg_one h2 hQ hdim.le hs hds
    have hsinv : s = s⁻¹ := eq_inv_of_mul_eq_one_right hss
    intro r hr hdr
    have hsr : s * r ∈ orthogonalGroup Q := (orthogonalGroup Q).mul_mem hs hr
    have hdsr : LinearEquiv.det (s * r) = -1 := by rw [map_mul, hds, hdr, mul_one]
    have h1 : (s * r) * (s * r) = 1 :=
      mul_self_eq_one_of_det_eq_neg_one h2 hQ hdim.le hsr hdsr
    have h2' : s * r * s = r⁻¹ := by
      calc s * r * s = (s * r * s * r) * r⁻¹ := by group
        _ = r⁻¹ := by rw [show s * r * s * r = (s * r) * (s * r) by group, h1, one_mul]
    calc s * r * s⁻¹ = s * r * s := by rw [← hsinv]
      _ = r⁻¹ := h2'

end QuadraticPlane

end CFSG.GroupTheory
