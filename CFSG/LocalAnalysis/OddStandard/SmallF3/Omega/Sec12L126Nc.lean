module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Conj

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec126_mem_normalizer_conjugate_iff {H : Subgroup G} {g x : G} :
    x ∈ normalizer (CFSG.conjugate H g : Set G) ↔ g * x * g⁻¹ ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hx w
    have h := hx (g⁻¹ * w * g)
    rw [mem_conjugate_iff, mem_conjugate_iff] at h
    have e1 : g * (g⁻¹ * w * g) * g⁻¹ = w := by group
    have e2 : g * (x * (g⁻¹ * w * g) * x⁻¹) * g⁻¹ = g * x * g⁻¹ * w * (g * x * g⁻¹)⁻¹ := by
      group
    rw [e1, e2] at h
    exact h
  · intro hx y
    have h := hx (g * y * g⁻¹)
    rw [mem_conjugate_iff, mem_conjugate_iff]
    have e2 : g * (x * y * x⁻¹) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ := by
      group
    rw [e2]
    exact h

theorem sec126_mem_centralizer_conjugate_iff {H : Subgroup G} {g x : G} :
    x ∈ centralizer (CFSG.conjugate H g : Set G) ↔ g * x * g⁻¹ ∈ centralizer (H : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx b hb
    have hb' : g⁻¹ * b * g ∈ (CFSG.conjugate H g : Set G) := by
      rw [SetLike.mem_coe, mem_conjugate_iff]
      have : g * (g⁻¹ * b * g) * g⁻¹ = b := by group
      rw [this]
      exact hb
    have h := hx _ hb'
    calc b * (g * x * g⁻¹) = g * ((g⁻¹ * b * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * b * g)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * b := by group
  · intro hx y hy
    have hy' : g * y * g⁻¹ ∈ H := (mem_conjugate_iff H g y).mp hy
    have h := hx _ hy'
    have h2 : g * (y * x) * g⁻¹ = g * (x * y) * g⁻¹ := by
      calc g * (y * x) * g⁻¹ = g * y * g⁻¹ * (g * x * g⁻¹) := by group
        _ = g * x * g⁻¹ * (g * y * g⁻¹) := h
        _ = g * (x * y) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)

theorem sec126_isElemAbelian_of_le {V D : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V)
    (hD : D ≤ V) : CFSG.Open.IsElemAbelian 2 D :=
  ⟨⟨⟨fun a b => Subtype.ext (hV.comm (hD a.2) (hD b.2))⟩⟩, fun x hx => hV.2 x (hD hx)⟩

end CFSG.OddStandard.SmallF3.Omega
