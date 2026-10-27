module

public import CFSG.FeitThompson.Foundations.NilpotentNormalizerCondition

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G]

theorem IsCentralSeries.subgroupOf {X : ℕ → Subgroup G} {r : ℕ} (hX : IsCentralSeries X r)
    (H : Subgroup G) : IsCentralSeries (fun i => (X i).subgroupOf H) r where
  bot := by simp [hX.bot]
  monotone _ _ hij := Subgroup.subgroupOf_mono H (hX.monotone hij)
  top := by simp [hX.top]
  commutator_le i _ := by
    rw [Subgroup.commutator_le]
    intro a _ b hb
    rw [Subgroup.mem_subgroupOf] at hb ⊢
    have h := hX.mul_mul_inv_mul_inv_mem (a : G) hb
    rw [commutatorElement_def]
    push_cast
    exact h

theorem isNilpotent_of_isCentralSeries {X : ℕ → Subgroup G} {r : ℕ} (hX : IsCentralSeries X r)
    (H : Subgroup G) : Group.IsNilpotent H :=
  (hX.subgroupOf H).isNilpotent

end CFSG.FeitThompson
