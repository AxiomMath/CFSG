module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Trans

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem index_two_rules {S K : Subgroup G} (hKS : K ≤ S) (hidx : K.relIndex S = 2) :
    (∀ a ∈ S, ∀ b ∈ S, a ∉ K → b ∉ K → a * b ∈ K) ∧ (∀ g ∈ S, ∀ q ∈ K, g * q * g⁻¹ ∈ K) := by
  have hidx' : (K.subgroupOf S).index = 2 := hidx
  have hprod : ∀ a ∈ S, ∀ b ∈ S, a ∉ K → b ∉ K → a * b ∈ K := by
    intro a ha b hb haS hbS
    have h := (Subgroup.mul_mem_iff_of_index_two hidx' (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)).2
      (by
        constructor
        · intro h1; exact absurd (mem_subgroupOf.1 h1) haS
        · intro h1; exact absurd (mem_subgroupOf.1 h1) hbS)
    exact mem_subgroupOf.1 h
  refine ⟨hprod, ?_⟩
  intro g hg q hq
  by_cases hgS : g ∈ K
  · exact K.mul_mem (K.mul_mem hgS hq) (K.inv_mem hgS)
  · have h1 : g * q ∉ K := by
      intro hmem
      apply hgS
      have : g = (g * q) * q⁻¹ := by group
      rw [this]
      exact K.mul_mem hmem (K.inv_mem hq)
    have h2 : g⁻¹ ∉ K := fun h => hgS (by simpa using K.inv_mem h)
    exact hprod (g * q) (S.mul_mem hg (hKS hq)) g⁻¹ (S.inv_mem hg) h1 h2

namespace Ctx3

variable {x : G} {T V H : Subgroup G} {f : G} (c : Ctx3 G x T V H f)
include c

theorem H_normal_Hstar [Finite G] {y : G} (hyS : y ∈ H ⊔ T) (hyH : y ∉ H) :
    ∀ s ∈ H ⊔ T, ∀ h ∈ H, s * h * s⁻¹ ∈ H :=
  (index_two_rules le_sup_left (c.Hstar_card_two hyS hyH).1).2

theorem y_x_comm_mem [Finite G] (hPn : ∀ s ∈ H ⊔ T, ∀ q ∈ Hzero H f, s * q * s⁻¹ ∈ Hzero H f)
    {y : G} (hyS : y ∈ H ⊔ T) (hyH : y ∉ H) : y * x * y⁻¹ * x⁻¹ ∈ Hzero H f := by
  have h1 : y * x * y⁻¹ ∈ H := c.H_normal_Hstar hyS hyH y hyS x c.x_mem_H
  obtain ⟨q, hq, h2 | h2⟩ := (c.mem_H_iff).1 h1
  · exfalso
    apply c.x_notin_H0
    have e : x = y⁻¹ * (y * x * y⁻¹) * y := by group
    rw [e, h2]
    have := hPn y⁻¹ ((H ⊔ T).inv_mem hyS) q hq
    rwa [inv_inv] at this
  · have e : y * x * y⁻¹ * x⁻¹ = q := by rw [h2]; group
    rw [e]; exact hq

theorem S_decomp [Finite G] {y : G} (hyS : y ∈ H ⊔ T) (hyH : y ∉ H) :
    ∀ s ∈ H ⊔ T, ∃ q ∈ Hzero H f, s = q ∨ s = q * x ∨ s = q * y ∨ s = q * x * y := by
  intro s hs
  by_cases hsH : s ∈ H
  · obtain ⟨q, hq, h | h⟩ := (c.mem_H_iff).1 hsH
    · exact ⟨q, hq, Or.inl h⟩
    · exact ⟨q, hq, Or.inr (Or.inl h)⟩
  · have hyinv : y⁻¹ ∉ H := fun h => hyH (by simpa using H.inv_mem h)
    have hprod := (index_two_rules le_sup_left (c.Hstar_card_two hyS hyH).1).1
    have h1 : s * y⁻¹ ∈ H := hprod s hs y⁻¹ ((H ⊔ T).inv_mem hyS) hsH hyinv
    obtain ⟨q, hq, h | h⟩ := (c.mem_H_iff).1 h1
    · refine ⟨q, hq, Or.inr (Or.inr (Or.inl ?_))⟩
      calc s = (s * y⁻¹) * y := by group
        _ = q * y := by rw [h]
    · refine ⟨q, hq, Or.inr (Or.inr (Or.inr ?_))⟩
      calc s = (s * y⁻¹) * y := by group
        _ = q * x * y := by rw [h]

theorem S_sq [Finite G] (hPn : ∀ s ∈ H ⊔ T, ∀ q ∈ Hzero H f, s * q * s⁻¹ ∈ Hzero H f)
    {y : G} (hyS : y ∈ H ⊔ T) (hyH : y ∉ H) (hy2 : y * y = 1) :
    ∀ s ∈ H ⊔ T, s * s ∈ Hzero H f := by
  intro s hs
  have hxS : x ∈ H ⊔ T := Subgroup.mem_sup_left c.x_mem_H
  obtain ⟨q, hq, h | h | h | h⟩ := c.S_decomp hyS hyH s hs
  · rw [h]
    exact (Hzero H f).mul_mem hq hq
  · rw [h]
    have e : q * x * (q * x) = q * (x * q * x⁻¹) * (x * x) := by group
    rw [e, c.x_sq, mul_one]
    exact (Hzero H f).mul_mem hq (hPn x hxS q hq)
  · rw [h]
    have e : q * y * (q * y) = q * (y * q * y⁻¹) * (y * y) := by group
    rw [e, hy2, mul_one]
    exact (Hzero H f).mul_mem hq (hPn y hyS q hq)
  · rw [h]
    have hq0 := c.y_x_comm_mem hPn hyS hyH
    have hxy : x * y ∈ H ⊔ T := (H ⊔ T).mul_mem hxS hyS
    have e : q * x * y * (q * x * y) =
        q * ((x * y) * q * (x * y)⁻¹) * ((x * (y * x * y⁻¹ * x⁻¹) * x⁻¹) * (x * x) * (y * y)) := by
      group
    rw [e, c.x_sq, hy2, mul_one, mul_one]
    exact (Hzero H f).mul_mem ((Hzero H f).mul_mem hq (hPn _ hxy q hq)) (hPn x hxS _ hq0)

end Ctx3

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
