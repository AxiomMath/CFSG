module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWOne
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup

variable {G : Type*} [Group G]

theorem isPGroup_zpowers_of_mul_self_eq_one {t : G} (ht : t * t = 1) :
    IsPGroup 2 (zpowers t) := by
  rintro ⟨_, k, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, sq, ht, one_zpow]

theorem mem_normalizer_centralizer_of_mem_normalizer {W : Subgroup G} {g : G}
    (hg : g ∈ normalizer (W : Set G)) :
    g ∈ normalizer ((centralizer (W : Set G) : Subgroup G) : Set G) := by
  have key : ∀ k : G, k ∈ normalizer (W : Set G) → ∀ h ∈ centralizer (W : Set G),
      k * h * k⁻¹ ∈ centralizer (W : Set G) := by
    intro k hk h hh
    rw [mem_centralizer_iff] at hh ⊢
    intro w hw
    have hw' : k⁻¹ * w * k ∈ W := by
      have := (mem_normalizer_iff.1 (inv_mem hk) w).1 hw
      rwa [inv_inv] at this
    have h1 := hh _ hw'
    calc w * (k * h * k⁻¹) = k * ((k⁻¹ * w * k) * h) * k⁻¹ := by group
      _ = k * (h * (k⁻¹ * w * k)) * k⁻¹ := by rw [h1]
      _ = k * h * k⁻¹ * w := by group
  rw [mem_normalizer_iff]
  intro h
  refine ⟨key g hg h, fun hh => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hh
  rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this

end CFSG.SeitzReduction.LinearPilot
