module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Group

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise Subgroup

variable {G : Type*} [Group G]

theorem coe_sup_inf_centralizer_eq {H Q P : Subgroup G}
    (hHn : (H.subgroupOf (H ⊔ Q)).Normal) (hdisj : Disjoint H Q)
    (hPH : P ≤ normalizer (H : Set G)) (hPQ : P ≤ normalizer (Q : Set G)) :
    (((H ⊔ Q) ⊓ centralizer (P : Set G) : Subgroup G) : Set G)
      = ((H ⊓ centralizer (P : Set G) : Subgroup G) : Set G)
        * ((Q ⊓ centralizer (P : Set G) : Subgroup G) : Set G) := by
  have hQH : Q ≤ normalizer (H : Set G) :=
    le_sup_right.trans (le_normalizer_of_normal_subgroupOf (hK := hHn) le_sup_left)
  have hset : ((H ⊔ Q : Subgroup G) : Set G) = (H : Set G) * (Q : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left H Q hQH
  apply Set.Subset.antisymm
  · intro x hx
    rw [SetLike.mem_coe, mem_inf] at hx
    obtain ⟨hxK, hxC⟩ := hx
    rw [← SetLike.mem_coe, hset] at hxK
    obtain ⟨h, hh, q, hq, rfl⟩ := hxK
    simp only [SetLike.mem_coe] at hh hq
    have hxC' : h * q ∈ centralizer (P : Set G) := hxC
    have key : ∀ a ∈ P, a * q * a⁻¹ = q := by
      intro a ha
      have hhH : a * h * a⁻¹ ∈ H := (mem_normalizer_iff.1 (hPH ha) h).1 hh
      have hqQ : a * q * a⁻¹ ∈ Q := (mem_normalizer_iff.1 (hPQ ha) q).1 hq
      have hcx : a * (h * q) = h * q * a := mem_centralizer_iff.1 hxC' a ha
      have hprod : (a * h * a⁻¹) * (a * q * a⁻¹) = h * q := by
        calc (a * h * a⁻¹) * (a * q * a⁻¹) = a * (h * q) * a⁻¹ := by group
          _ = h * q := by rw [hcx]; group
      have hu : h⁻¹ * (a * h * a⁻¹) = q * (a * q * a⁻¹)⁻¹ := by
        calc h⁻¹ * (a * h * a⁻¹)
            = h⁻¹ * ((a * h * a⁻¹) * (a * q * a⁻¹)) * (a * q * a⁻¹)⁻¹ := by group
          _ = h⁻¹ * (h * q) * (a * q * a⁻¹)⁻¹ := by rw [hprod]
          _ = q * (a * q * a⁻¹)⁻¹ := by group
      have huH : h⁻¹ * (a * h * a⁻¹) ∈ H := mul_mem (inv_mem hh) hhH
      have huQ : h⁻¹ * (a * h * a⁻¹) ∈ Q := hu ▸ mul_mem hq (inv_mem hqQ)
      have h1 : h⁻¹ * (a * h * a⁻¹) = 1 := Subgroup.disjoint_def.1 hdisj huH huQ
      have hq1 : q * (a * q * a⁻¹)⁻¹ = 1 := by rw [← hu, h1]
      exact (mul_inv_eq_one.1 hq1).symm
    have hqC : q ∈ centralizer (P : Set G) := by
      rw [mem_centralizer_iff]
      intro a ha
      calc a * q = (a * q * a⁻¹) * a := by group
        _ = q * a := by rw [key a ha]
    have hhC : h ∈ centralizer (P : Set G) := by
      have hheq : h = (h * q) * q⁻¹ := by group
      rw [hheq]
      exact mul_mem hxC' (inv_mem hqC)
    exact ⟨h, mem_inf.2 ⟨hh, hhC⟩, q, mem_inf.2 ⟨hq, hqC⟩, rfl⟩
  · rintro x ⟨h, hh, q, hq, rfl⟩
    simp only [SetLike.mem_coe, mem_inf] at hh hq ⊢
    exact ⟨mul_mem (mem_sup_left hh.1) (mem_sup_right hq.1), mul_mem hh.2 hq.2⟩

theorem sup_inf_centralizer_eq_of_inf_centralizer_eq_bot {H Q P : Subgroup G}
    (hHn : (H.subgroupOf (H ⊔ Q)).Normal) (hdisj : Disjoint H Q)
    (hPH : P ≤ normalizer (H : Set G)) (hPQ : P ≤ normalizer (Q : Set G))
    (hCQ : Q ⊓ centralizer (P : Set G) = ⊥) :
    (H ⊔ Q) ⊓ centralizer (P : Set G) = H ⊓ centralizer (P : Set G) := by
  apply SetLike.coe_injective
  rw [coe_sup_inf_centralizer_eq hHn hdisj hPH hPQ, hCQ]
  simp

theorem sup_inf_centralizer_le_of_inf_centralizer_eq_bot {H Q P : Subgroup G}
    (hHn : (H.subgroupOf (H ⊔ Q)).Normal) (hdisj : Disjoint H Q)
    (hPH : P ≤ normalizer (H : Set G)) (hPQ : P ≤ normalizer (Q : Set G))
    (hCQ : Q ⊓ centralizer (P : Set G) = ⊥) :
    (H ⊔ Q) ⊓ centralizer (P : Set G) ≤ H := by
  rw [sup_inf_centralizer_eq_of_inf_centralizer_eq_bot hHn hdisj hPH hPQ hCQ]
  exact inf_le_left

end CFSG.FeitThompson
