module

import CFSG.FeitThompson.Foundations.NormalContainsMinimalNormal
import CFSG.FeitThompson.Foundations.MinimalNormalSolvableElemAbelian
import CFSG.FeitThompson.Foundations.SolvableSubgroupSolvable
public import Mathlib.GroupTheory.Solvable
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Nat.Prime.Defs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G]

theorem minimal_normal_ne_bot_iff {N : Subgroup G} :
    Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥) N ↔
      N.Normal ∧ N ≠ ⊥ ∧ ∀ K : Subgroup G, K.Normal → K < N → K = ⊥ := by
  refine ⟨fun h => ⟨h.1.1, h.1.2, fun K hKn hKN => ?_⟩,
    fun h => ⟨⟨h.1, h.2.1⟩, fun K hK hKN => ?_⟩⟩
  · by_contra hKb
    exact absurd (h.2 ⟨hKn, hKb⟩ hKN.le) hKN.not_ge
  · exact (eq_of_normal_of_le_of_forall_lt_eq_bot h.2.2 hK.1 hKN hK.2).ge

theorem exists_minimal_normal_ne_bot [Finite G] [Nontrivial G] :
    ∃ N : Subgroup G, Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥) N := by
  obtain ⟨N, hNn, hNb, hmin⟩ := exists_normal_ne_bot_forall_lt_eq_bot (G := G)
  exact ⟨N, minimal_normal_ne_bot_iff.2 ⟨hNn, hNb, hmin⟩⟩

theorem exists_prime_nonempty_mulEquiv_of_minimal_normal_ne_bot [Finite G] [Group.IsSolvable G]
    {N : Subgroup G} (hN : Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥) N) :
    ∃ p d : ℕ, p.Prime ∧ 1 ≤ d ∧ Nonempty (↥N ≃* Multiplicative (Fin d → ZMod p)) := by
  obtain ⟨hNn, hNb, hmin⟩ := minimal_normal_ne_bot_iff.1 hN
  have _inst : N.Normal := hNn
  have : Group.IsSolvable ↥N := isSolvable_of_le (K := (⊤ : Subgroup G)) le_top
  exact exists_prime_nonempty_mulEquiv_of_isSolvable_of_forall_normal_lt_eq_bot hNb hmin

theorem exists_prime_card_eq_pow_of_minimal_normal_ne_bot [Finite G] [Group.IsSolvable G]
    {N : Subgroup G} (hN : Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥) N) :
    ∃ p d : ℕ, p.Prime ∧ 1 ≤ d ∧ Nat.card ↥N = p ^ d := by
  obtain ⟨p, d, hp, hd, ⟨e⟩⟩ := exists_prime_nonempty_mulEquiv_of_minimal_normal_ne_bot hN
  have _inst : Fact p.Prime := ⟨hp⟩
  refine ⟨p, d, hp, hd, ?_⟩
  rw [Nat.card_eq_of_bijective e e.bijective]
  simp [Nat.card_eq_fintype_card]

theorem exists_minimal_normal_ne_bot_nonempty_mulEquiv [Finite G] [Nontrivial G]
    [Group.IsSolvable G] :
    ∃ N : Subgroup G, Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥) N ∧
      ∃ p d : ℕ, p.Prime ∧ 1 ≤ d ∧ Nonempty (↥N ≃* Multiplicative (Fin d → ZMod p)) := by
  obtain ⟨N, hN⟩ := exists_minimal_normal_ne_bot (G := G)
  exact ⟨N, hN, exists_prime_nonempty_mulEquiv_of_minimal_normal_ne_bot hN⟩

end CFSG.FeitThompson

