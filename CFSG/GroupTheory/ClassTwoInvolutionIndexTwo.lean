module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped commutatorElement

variable {Q : Type*} [Group Q]

theorem apply_mul_inv_mem_center_of_index_eq_two_of_class_two [Finite Q]
    (hsqc : ∀ v : Q, v * v ∈ center Q) (hcom : ∀ a b : Q, ⁅a, b⁆ ∈ center Q)
    (σ : MulAut Q) (hσ : ∀ x, σ (σ x) = x) (hZ : ∀ c ∈ center Q, σ c = c) {D : Subgroup Q}
    (hDmem : ∀ x, x ∈ D ↔ σ x = x) (hD : D.index = 2) (x : Q) :
    σ x * x⁻¹ ∈ center Q := by
  have hσD : ∀ v, σ v ∈ D ↔ v ∈ D := by
    intro v
    rw [hDmem, hDmem, hσ]
    exact eq_comm
  have hcD : ∀ v, v⁻¹ * σ v ∈ D := by
    intro v
    rw [Subgroup.mul_mem_iff_of_index_two hD, inv_mem_iff, hσD]
  have hc2 : ∀ v, (v⁻¹ * σ v) * (v⁻¹ * σ v) = 1 := by
    intro v
    have h1 : σ (v⁻¹ * σ v) = v⁻¹ * σ v := (hDmem _).mp (hcD v)
    rw [map_mul, map_inv, hσ] at h1
    calc (v⁻¹ * σ v) * (v⁻¹ * σ v) = (v⁻¹ * σ v) * ((σ v)⁻¹ * v) := by rw [h1]
      _ = 1 := by group
  have hcomm : ∀ v, (v⁻¹ * σ v) * v = v * (v⁻¹ * σ v) := by
    intro v
    set c : Q := v⁻¹ * σ v with hc
    have hvc : σ v = v * c := by rw [hc]; group
    have hsq : σ v * σ v = v * v := by
      rw [← map_mul]
      exact hZ _ (hsqc v)
    have hcvc : c * v * c = v := by
      have h : v * (c * v * c) = v * v := by
        calc v * (c * v * c) = (v * c) * (v * c) := by group
          _ = σ v * σ v := by rw [hvc]
          _ = v * v := hsq
      exact mul_left_cancel h
    calc c * v = c * v * (c * c) := by rw [hc2 v, mul_one]
      _ = (c * v * c) * c := by group
      _ = v * c := by rw [hcvc]
  by_cases hall : ∀ v, v ∈ D
  · rw [(hDmem x).mp (hall x), mul_inv_cancel]
    exact one_mem _
  push Not at hall
  obtain ⟨u, hu⟩ := hall
  set c : Q := u⁻¹ * σ u with hc
  have hcu : c * u = u * c := hcomm u
  have hcd : ∀ d ∈ D, c * d = d * c := by
    intro d hd
    have hσd : σ d = d := (hDmem d).mp hd
    have hv := hcomm (u * d)
    have hcv : (u * d)⁻¹ * σ (u * d) = d⁻¹ * c * d := by
      rw [map_mul, hσd, hc]; group
    rw [hcv] at hv
    set ζ : Q := c⁻¹ * (d⁻¹ * c * d) with hζ
    have hζc : ζ ∈ center Q := by
      have h1 : ζ = ⁅c⁻¹, d⁻¹⁆ := by rw [hζ, commutatorElement_def]; group
      rw [h1]
      exact hcom _ _
    have hζ' := mem_center_iff.mp hζc
    have hdcd : d⁻¹ * c * d = c * ζ := by rw [hζ]; group
    rw [hdcd] at hv
    have h2 : c * (u * d) = u * d * c := by
      have h3 : c * (u * d) * ζ = u * d * c * ζ := by
        calc c * (u * d) * ζ = c * (ζ * (u * d)) := by rw [← hζ' (u * d)]; group
          _ = c * ζ * (u * d) := by group
          _ = u * d * (c * ζ) := hv
          _ = u * d * c * ζ := by group
      exact mul_right_cancel h3
    have h4 : u * (c * d) = u * (d * c) := by
      calc u * (c * d) = (u * c) * d := by group
        _ = (c * u) * d := by rw [hcu]
        _ = c * (u * d) := by group
        _ = u * d * c := h2
        _ = u * (d * c) := by group
    exact mul_left_cancel h4
  have hcc : c ∈ center Q := by
    rw [mem_center_iff]
    intro v
    by_cases hv : v ∈ D
    · exact (hcd v hv).symm
    · have hud : u⁻¹ * v ∈ D := by
        rw [Subgroup.mul_mem_iff_of_index_two hD]
        simp [hu, hv]
      have h1 := hcd _ hud
      calc v * c = u * (u⁻¹ * v) * c := by group
        _ = u * ((u⁻¹ * v) * c) := by group
        _ = u * (c * (u⁻¹ * v)) := by rw [← h1]
        _ = (u * c) * (u⁻¹ * v) := by group
        _ = (c * u) * (u⁻¹ * v) := by rw [hcu]
        _ = c * v := by group
  by_cases hx : x ∈ D
  · rw [(hDmem x).mp hx, mul_inv_cancel]
    exact one_mem _
  obtain ⟨d, hdD, rfl⟩ : ∃ d ∈ D, x = u * d := by
    refine ⟨u⁻¹ * x, ?_, by group⟩
    rw [Subgroup.mul_mem_iff_of_index_two hD]
    simp [hu, hx]
  have hσu : σ u = u * c := by rw [hc]; group
  have : σ (u * d) * (u * d)⁻¹ = c := by
    rw [map_mul, (hDmem d).mp hdD, hσu]
    have h := mem_center_iff.mp hcc u
    calc u * c * d * (u * d)⁻¹ = u * c * u⁻¹ := by group
      _ = c * u * u⁻¹ := by rw [h]
      _ = c := by group
  rw [this]
  exact hcc

end CFSG.GroupTheory
