module

public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Index
public import Mathlib.SetTheory.Cardinal.Finite
public import CFSG.FeitThompson.Foundations.CommutatorMonotone

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G] (A B : Subgroup G)

theorem inv_mul_inv_mul_mul_mem_inf [A.Normal] [B.Normal] {a b : G} (ha : a ∈ A) (hb : b ∈ B) :
    a⁻¹ * b⁻¹ * a * b ∈ A ⊓ B := by
  refine ⟨?_, ?_⟩
  · have : a⁻¹ * b⁻¹ * a * b = a⁻¹ * (b⁻¹ * a * b) := by simp [mul_assoc]
    rw [this]
    exact A.mul_mem (A.inv_mem ha) (by simpa using ‹A.Normal›.conj_mem a ha b⁻¹)
  · exact B.mul_mem (by simpa using ‹B.Normal›.conj_mem b⁻¹ (B.inv_mem hb) a⁻¹) hb

theorem closure_inv_mul_inv_mul_mul_le_inf [A.Normal] [B.Normal] :
    Subgroup.closure {g : G | ∃ a ∈ A, ∃ b ∈ B, a⁻¹ * b⁻¹ * a * b = g} ≤ A ⊓ B :=
  Subgroup.closure_le _ |>.2 <| by
    rintro g ⟨a, ha, b, hb, rfl⟩
    exact inv_mul_inv_mul_mul_mem_inf A B ha hb

theorem mul_comm_of_normal_of_coprime_natCard [A.Normal] [B.Normal]
    (h : (Nat.card A).Coprime (Nat.card B)) {a b : G} (ha : a ∈ A) (hb : b ∈ B) :
    a * b = b * a :=
  Subgroup.commute_of_normal_of_disjoint A B ‹A.Normal› ‹B.Normal›
    (Subgroup.disjoint_of_coprime_natCard h) a b ha hb

theorem commutator_eq_bot_of_normal_of_coprime_natCard [A.Normal] [B.Normal]
    (h : (Nat.card A).Coprime (Nat.card B)) : ⁅A, B⁆ = ⊥ :=
  Subgroup.commutator_eq_bot_of_disjoint (Subgroup.disjoint_of_coprime_natCard h)

end

end CFSG.FeitThompson
