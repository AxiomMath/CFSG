module

public import Mathlib.GroupTheory.Nilpotent

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G]

structure IsCentralSeries (X : ℕ → Subgroup G) (r : ℕ) : Prop where
  bot : X 0 = ⊥
  monotone : Monotone X
  top : X r = ⊤
  commutator_le : ∀ i < r, ⁅(⊤ : Subgroup G), X (i + 1)⁆ ≤ X i

namespace IsCentralSeries

variable {X : ℕ → Subgroup G} {r : ℕ}

theorem eq_top_of_le (hX : IsCentralSeries X r) {i : ℕ} (hi : r ≤ i) : X i = ⊤ :=
  top_le_iff.mp (hX.top ▸ hX.monotone hi)

theorem mul_mul_inv_mul_inv_mem (hX : IsCentralSeries X r) (g : G) {x : G} {i : ℕ}
    (hx : x ∈ X (i + 1)) : g * x * g⁻¹ * x⁻¹ ∈ X i := by
  rcases lt_or_ge i r with hi | hi
  · have h := hX.commutator_le i hi
      (Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := X (i + 1)) (mem_top g) hx)
    rwa [commutatorElement_def] at h
  · rw [hX.eq_top_of_le hi]
    exact mem_top _

theorem normal (hX : IsCentralSeries X r) (i : ℕ) : (X i).Normal := by
  cases i with
  | zero => rw [hX.bot]; infer_instance
  | succ i =>
    refine ⟨fun n hn g => ?_⟩
    have h : g * n * g⁻¹ * n⁻¹ ∈ X i := hX.mul_mul_inv_mul_inv_mem g hn
    have h' : g * n * g⁻¹ * n⁻¹ * n ∈ X (i + 1) := mul_mem (hX.monotone (Nat.le_succ i) h) hn
    simpa [mul_assoc] using h'

theorem isNilpotent (hX : IsCentralSeries X r) : Group.IsNilpotent G := by
  rw [Subgroup.nilpotent_iff_finite_ascending_central_series]
  refine ⟨r, X, ⟨hX.bot, ?_⟩, hX.top⟩
  intro x n hx g
  have h := (X n).inv_mem (hX.mul_mul_inv_mul_inv_mem g hx)
  rw [commutatorElement_def]
  simpa [mul_assoc] using h

end IsCentralSeries

theorem isNilpotent_iff_exists_isCentralSeries :
    Group.IsNilpotent G ↔ ∃ (X : ℕ → Subgroup G) (r : ℕ), IsCentralSeries X r := by
  refine ⟨fun _ => ?_, fun ⟨_, _, hX⟩ => hX.isNilpotent⟩
  obtain ⟨n, hn⟩ := Group.IsNilpotent.nilpotent G
  refine ⟨Subgroup.upperCentralSeries G, n, Subgroup.upperCentralSeries_zero G,
    Subgroup.upperCentralSeries_mono G, hn, fun i _ => ?_⟩
  exact (Subgroup.commutator_comm _ _).trans_le
    (Subgroup.commutator_upperCentralSeries_top_le G i)

theorem IsCentralSeries.lt_normalizer {X : ℕ → Subgroup G} {r : ℕ} (hX : IsCentralSeries X r)
    {H : Subgroup G} (hH : H < ⊤) : H < normalizer (H : Set G) :=
  have : Group.IsNilpotent G := hX.isNilpotent
  Group.normalizerCondition_of_isNilpotent H hH

end

end CFSG.FeitThompson
