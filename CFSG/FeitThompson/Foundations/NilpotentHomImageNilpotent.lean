module
public import Mathlib.GroupTheory.Nilpotent
import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G H : Type*} [Group G] [Group H]

theorem isNilpotent_iff_exists_central_series :
    Group.IsNilpotent G ↔ ∃ (r : ℕ) (X : ℕ → Subgroup G), X 0 = ⊥ ∧ X r = ⊤ ∧
      (∀ i < r, X i ≤ X (i + 1)) ∧ (∀ i, (X i).Normal) ∧
      ∀ i < r, Subgroup.closure {g : G | ∃ a ∈ (⊤ : Subgroup G), ∃ b ∈ X (i + 1),
        a⁻¹ * b⁻¹ * a * b = g} ≤ X i := by
  constructor
  · intro h
    refine ⟨Group.nilpotencyClass G, Subgroup.upperCentralSeries G,
      Subgroup.upperCentralSeries_zero G, Subgroup.upperCentralSeries_nilpotencyClass,
      fun i _ => Subgroup.upperCentralSeries_mono G (Nat.le_succ i),
      fun i => inferInstance, fun i _ => ?_⟩
    rw [closure_setOf_inv_mul_inv_mul_mul, Subgroup.commutator_comm]
    exact Subgroup.commutator_upperCentralSeries_top_le G i
  · rintro ⟨r, X, h0, hr, -, -, hcomm⟩
    rw [Subgroup.nilpotent_iff_finite_ascending_central_series]
    refine ⟨r, fun i => X (min i r), ⟨by simpa using h0, fun x n hx g => ?_⟩, by simp [hr]⟩
    simp only at hx ⊢
    rcases lt_or_ge n r with hn | hn
    · rw [min_eq_left hn.le]
      rw [min_eq_left (Nat.succ_le_of_lt hn)] at hx
      refine hcomm n hn ?_
      rw [closure_setOf_inv_mul_inv_mul_mul, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hx (Subgroup.mem_top g)
    · rw [min_eq_right hn, hr]
      exact Subgroup.mem_top _

theorem isNilpotent_range (f : G →* H) [Group.IsNilpotent G] :
    Group.IsNilpotent f.range :=
  Group.nilpotent_of_surjective f.rangeRestrict f.rangeRestrict_surjective

theorem isNilpotent_map (f : G →* H) (A : Subgroup G) [Group.IsNilpotent A] :
    Group.IsNilpotent (A.map f) :=
  Group.nilpotent_of_surjective (f.subgroupMap A) (f.subgroupMap_surjective A)

end CFSG.FeitThompson
