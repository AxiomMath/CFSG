module

public import CFSG.FeitThompson.Definitions.DadeData
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Complex.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G] [Fintype G]

noncomputable def dadeAverage (A : Set G) (H : G → Subgroup G) (χ : G → ℂ) : G → ℂ :=
  A.indicator fun a =>
    (Nat.card ↥(H a) : ℂ)⁻¹ * ∑ u : G, (H a : Set G).indicator (fun u => χ (u * a)) u

variable {A : Set G} {H : G → Subgroup G} {χ : G → ℂ} {a x : G}

theorem dadeAverage_apply_of_mem [DecidablePred (· ∈ H a)] (ha : a ∈ A) (χ : G → ℂ) :
    dadeAverage A H χ a = (Nat.card ↥(H a) : ℂ)⁻¹ * ∑ u : ↥(H a), χ (u * a) := by
  rw [dadeAverage, Set.indicator_of_mem ha]
  congr 1
  rw [Finset.sum_indicator_eq_sum_filter]
  exact Finset.sum_subtype _ (by simp) _

theorem dadeAverage_apply_of_mem' [DecidablePred (· ∈ H a)] (ha : a ∈ A) (χ : G → ℂ) :
    dadeAverage A H χ a =
      (Nat.card ↥(H a) : ℂ)⁻¹ * ∑ u : G, if u ∈ H a then χ (u * a) else 0 := by
  rw [dadeAverage, Set.indicator_of_mem ha]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Set.indicator_apply]
  simp

theorem dadeAverage_eq_zero_of_notMem (h : x ∉ A) : dadeAverage A H χ x = 0 :=
  Set.indicator_of_notMem h _

theorem support_dadeAverage_subset : Function.support (dadeAverage A H χ) ⊆ A :=
  Set.support_indicator_subset

theorem dadeAverage_eq_zero_of_notMem_subgroup {L : Subgroup G} (hD : IsDadeData L A H)
    (hx : x ∉ L) : dadeAverage A H χ x = 0 :=
  dadeAverage_eq_zero_of_notMem fun h => hx (hD.mem_of_mem h)

theorem dadeAverage_apply_of_H_eq_bot (ha : a ∈ A) (hH : H a = ⊥) (χ : G → ℂ) :
    dadeAverage A H χ a = χ a := by
  classical
  rw [dadeAverage_apply_of_mem' ha, hH]
  simp

theorem dadeAverage_apply_of_mem_comm [DecidablePred (· ∈ H a)] {L : Subgroup G}
    (hD : IsDadeData L A H) (ha : a ∈ A) (χ : G → ℂ) :
    dadeAverage A H χ a = (Nat.card ↥(H a) : ℂ)⁻¹ * ∑ u : ↥(H a), χ (a * u) := by
  rw [dadeAverage_apply_of_mem ha]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [(hD.le_centralizer ha u.2) a rfl]

theorem dadeAverage_apply_of_eq_on (ha : a ∈ A) {c : ℂ} (hχ : ∀ u ∈ H a, χ (u * a) = c) :
    dadeAverage A H χ a = c := by
  classical
  rw [dadeAverage_apply_of_mem ha,
    Finset.sum_congr rfl (fun (u : ↥(H a)) _ => hχ (u : G) u.2),
    Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, nsmul_eq_mul,
    inv_mul_cancel_left₀]
  exact Nat.cast_ne_zero.2 Fintype.card_ne_zero

theorem dadeAverage_zero : dadeAverage A H (0 : G → ℂ) = 0 := by
  funext x
  by_cases hx : x ∈ A
  · exact dadeAverage_apply_of_eq_on hx fun _ _ => rfl
  · rw [dadeAverage_eq_zero_of_notMem hx, Pi.zero_apply]

noncomputable def dadeAverageₗ (A : Set G) (H : G → Subgroup G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun := dadeAverage A H
  map_add' χ ψ := by
    classical
    funext x
    by_cases hx : x ∈ A
    · simp only [Pi.add_apply, dadeAverage_apply_of_mem hx, Finset.sum_add_distrib, mul_add]
    · simp [dadeAverage_eq_zero_of_notMem hx]
  map_smul' c χ := by
    classical
    funext x
    by_cases hx : x ∈ A
    · simp only [Pi.smul_apply, dadeAverage_apply_of_mem hx, smul_eq_mul, RingHom.id_apply,
        Finset.mul_sum, mul_left_comm]
    · simp [dadeAverage_eq_zero_of_notMem hx]

@[simp]
theorem dadeAverageₗ_apply (A : Set G) (H : G → Subgroup G) (χ : G → ℂ) :
    dadeAverageₗ A H χ = dadeAverage A H χ := (rfl)

theorem dadeAverage_add (χ ψ : G → ℂ) :
    dadeAverage A H (χ + ψ) = dadeAverage A H χ + dadeAverage A H ψ :=
  (dadeAverageₗ A H).map_add χ ψ

theorem dadeAverage_smul (c : ℂ) (χ : G → ℂ) :
    dadeAverage A H (c • χ) = c • dadeAverage A H χ :=
  (dadeAverageₗ A H).map_smul c χ

end CFSG.FeitThompson
