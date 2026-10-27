module

public import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.SetLike.Fintype
public import Mathlib.Basic.Finite.Defs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G]

theorem exists_normal_ne_bot_le_forall_lt_eq_bot [Finite G] {N : Subgroup G} (hN : N.Normal)
    (hN' : N ≠ ⊥) :
    ∃ M : Subgroup G, M.Normal ∧ M ≠ ⊥ ∧ M ≤ N ∧
      ∀ K : Subgroup G, K.Normal → K < M → K = ⊥ := by
  obtain ⟨M, ⟨hMn, hMb, hMN⟩, hmin⟩ :=
    (wellFounded_lt (α := Subgroup G)).has_min
      {M : Subgroup G | M.Normal ∧ M ≠ ⊥ ∧ M ≤ N} ⟨N, hN, hN', le_rfl⟩
  refine ⟨M, hMn, hMb, hMN, fun K hKn hKM => ?_⟩
  by_contra hKb
  exact hmin K ⟨hKn, hKb, hKM.le.trans hMN⟩ hKM

theorem exists_minimal_normal_ne_bot_le [Finite G] {N : Subgroup G} (hN : N.Normal) (hN' : N ≠ ⊥) :
    ∃ M : Subgroup G, Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥ ∧ K ≤ N) M := by
  obtain ⟨M, hM, hmin⟩ :=
    (wellFounded_lt (α := Subgroup G)).has_min
      {M : Subgroup G | M.Normal ∧ M ≠ ⊥ ∧ M ≤ N} ⟨N, hN, hN', le_rfl⟩
  exact ⟨M, hM, fun K hK hKM => (eq_of_le_of_not_lt hKM (hmin K hK)).ge⟩

theorem exists_normal_ne_bot_forall_lt_eq_bot [Finite G] [Nontrivial G] :
    ∃ M : Subgroup G, M.Normal ∧ M ≠ ⊥ ∧ ∀ K : Subgroup G, K.Normal → K < M → K = ⊥ := by
  obtain ⟨M, hMn, hMb, -, hmin⟩ :=
    exists_normal_ne_bot_le_forall_lt_eq_bot (N := (⊤ : Subgroup G)) Subgroup.normal_top top_ne_bot
  exact ⟨M, hMn, hMb, hmin⟩

theorem eq_of_normal_of_le_of_forall_lt_eq_bot {M : Subgroup G}
    (hM : ∀ K : Subgroup G, K.Normal → K < M → K = ⊥) {K : Subgroup G} (hKn : K.Normal)
    (hKM : K ≤ M) (hKb : K ≠ ⊥) : K = M :=
  eq_of_le_of_not_lt hKM fun h => hKb (hM K hKn h)

end CFSG.FeitThompson
