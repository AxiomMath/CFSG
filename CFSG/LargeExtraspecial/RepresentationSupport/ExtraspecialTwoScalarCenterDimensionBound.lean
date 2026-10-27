module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoOperatorIndependent

public section

namespace CFSG.LargeExtraspecial

namespace RepresentationSupport

namespace ExtraspecialTwoScalarCenterDimensionBound

theorem dimension_lower_bound {F : Type*} [Field F] (hF : (2 : F) ≠ 0)
    {W : Type*} [AddCommGroup W] [Module F W] [Nontrivial W] [Module.Finite F W]
    {E : Type*} [Group E] [Finite E] (hE : CFSG.IsExtraspecialPGroup 2 E)
    {w : ℕ} (hcard : Nat.card E = 2 ^ (1 + 2 * w))
    (σ : Representation F E W) (z : E) (hz : z ∈ Subgroup.center E) (hz1 : z ≠ 1)
    (hzScalar : σ z = -LinearMap.id) :
    2 ^ w ≤ Module.finrank F W := by
  classical
  have hcen : Nat.card (Subgroup.center E) = 2 := hE.2.2.2
  have hq : Nat.card (E ⧸ Subgroup.center E) = 2 ^ (2 * w) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center E)
    rw [hcard, hcen, pow_add] at h
    have h2 : (2 : ℕ) ^ (2 * w) * 2 = Nat.card (E ⧸ Subgroup.center E) * 2 := by
      rw [← h]; ring
    exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h2).symm
  let r : E ⧸ Subgroup.center E → E := Quotient.out
  have hr : ∀ q, (QuotientGroup.mk (r q) : E ⧸ Subgroup.center E) = q := fun q => Quotient.out_eq' q
  have hli := ExtraspecialTwoOperatorIndependent.linearIndependent hF hE σ z hz hz1 hzScalar r hr
  haveI : Fintype (E ⧸ Subgroup.center E) := Fintype.ofFinite _
  have h1 := hli.fintype_card_le_finrank
  rw [← Nat.card_eq_fintype_card, hq, Module.finrank_linearMap]  at h1
  have h3 : 2 ^ w * 2 ^ w ≤ Module.finrank F W * Module.finrank F W := by
    calc 2 ^ w * 2 ^ w = 2 ^ (2 * w) := by rw [← pow_add]; ring_nf
      _ ≤ _ := h1
  exact Nat.mul_self_le_mul_self_iff.1 h3

end ExtraspecialTwoScalarCenterDimensionBound

end RepresentationSupport

end CFSG.LargeExtraspecial
