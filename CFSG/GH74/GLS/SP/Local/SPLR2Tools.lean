module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup

section InvolutionTools

variable {G : Type} [Group G]

theorem invol_decomp [Finite G] (z : G) (hz : z * z = 1) (Q : Subgroup G)
    (hQ : ∀ q ∈ Q, z * q * z⁻¹ ∈ Q) (hodd : Odd (Nat.card ↥Q)) {q : G} (hq : q ∈ Q) :
    ∃ c ∈ Q, ∃ s ∈ Q, z * c * z⁻¹ = c ∧ z * s * z⁻¹ = s⁻¹ ∧ q = c * s := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  set u : G := q⁻¹ * (z * q * z⁻¹) with hu
  have huQ : u ∈ Q := Q.mul_mem (Q.inv_mem hq) (hQ q hq)
  have hzu : z * u * z⁻¹ = u⁻¹ := by
    rw [hu]
    have : z * (q⁻¹ * (z * q * z⁻¹)) * z⁻¹ = (z * q⁻¹ * z⁻¹) * ((z * z) * q * (z * z)⁻¹) := by group
    rw [this, hz]
    simp only [inv_one, mul_one, one_mul]
    have : (z * q⁻¹ * z⁻¹) = (z * q * z⁻¹)⁻¹ := by group
    rw [this]; group
  have hordu : Odd (orderOf u) := by
    have : orderOf u ∣ Nat.card ↥Q := by
      have := Subgroup.orderOf_dvd_natCard Q huQ
      exact this
    exact Odd.of_dvd_nat hodd this
  obtain ⟨m, hm⟩ := hordu
  set r : G := u ^ (m + 1) with hr
  have hrsq : r * r = u := by
    rw [hr, ← pow_add]
    have : (m + 1) + (m + 1) = orderOf u + 1 := by omega
    rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
  have hrQ : r ∈ Q := Q.pow_mem huQ _
  have hzr : z * r * z⁻¹ = r⁻¹ := by
    have : z * r * z⁻¹ = (z * u * z⁻¹) ^ (m + 1) := by rw [hr, conj_pow]
    rw [this, hzu, inv_pow]
  refine ⟨q * r, Q.mul_mem hq hrQ, r⁻¹, Q.inv_mem hrQ, ?_, ?_, by group⟩
  ·
    have e : z * (q * r) * z⁻¹ = (z * q * z⁻¹) * (z * r * z⁻¹) := by group
    rw [e, hzr]
    have hq' : z * q * z⁻¹ = q * u := by rw [hu]; group
    rw [hq']
    calc q * u * r⁻¹ = q * (r * r) * r⁻¹ := by rw [hrsq]
      _ = q * r := by group
  · rw [show z * r⁻¹ * z⁻¹ = (z * r * z⁻¹)⁻¹ by group, hzr, inv_inv]

end InvolutionTools


end CFSG.GH74.GLS.SP.Local
