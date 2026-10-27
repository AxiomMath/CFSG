module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup

theorem exists_mem_normalizer_sq_mem {G : Type*} [Group G] [Finite G] {U W : Subgroup G}
    (hUW : U ≤ W) (hne : U ≠ W) (hW : IsPGroup 2 ↥W) :
    ∃ w ∈ W, w ∉ U ∧ w ∈ Subgroup.normalizer (U : Set G) ∧ w ^ 2 ∈ U := by
  have : Group.IsNilpotent ↥W := hW.isNilpotent
  have hlt : U.subgroupOf W < ⊤ :=
    lt_top_iff_ne_top.2 fun h => hne (le_antisymm hUW (subgroupOf_eq_top.1 h))
  obtain ⟨y, hyN, hyU⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hyN' : (y : G) ∈ normalizer (U : Set G) := by
    have : y ∈ (normalizer (U : Set G)).subgroupOf W := by
      rw [subgroupOf_normalizer_eq hUW]
      exact hyN
    exact this
  have key : ∀ k : ℕ, ∀ x : G, x ∈ W → x ∈ normalizer (U : Set G) → x ∉ U → x ^ 2 ^ k ∈ U →
      ∃ w ∈ W, w ∉ U ∧ w ∈ normalizer (U : Set G) ∧ w ^ 2 ∈ U := by
    intro k
    induction k with
    | zero => exact fun x _ _ hx h => absurd (by simpa using h) hx
    | succ k ih =>
      intro x hxW hxN hxU h
      by_cases hk : x ^ 2 ^ k ∈ U
      · exact ih x hxW hxN hxU hk
      · exact ⟨x ^ 2 ^ k, pow_mem hxW _, hk, pow_mem hxN _, by rwa [← pow_mul, ← pow_succ]⟩
  obtain ⟨k, hk⟩ := hW y
  refine key k y y.2 hyN' hyU ?_
  have : (y : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [this]
  exact U.one_mem

end CFSG.GH74.GLS.IVK.Proofs2
