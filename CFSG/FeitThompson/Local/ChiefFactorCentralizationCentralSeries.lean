module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.FeitThompson.Foundations.CommutatorMonotone

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G]

structure IsChiefFactor (X Y : Subgroup G) : Prop where
  normal_num : X.Normal
  normal_den : Y.Normal
  lt : Y < X
  not_lt_lt : ∀ Z : Subgroup G, Z.Normal → Y < Z → ¬Z < X

namespace IsChiefFactor

theorem le {X Y : Subgroup G} (h : IsChiefFactor X Y) : Y ≤ X := h.lt.le

theorem ne' {X Y : Subgroup G} (h : IsChiefFactor X Y) : Y ≠ X := h.lt.ne

theorem num_ne_bot {X Y : Subgroup G} (h : IsChiefFactor X Y) : X ≠ ⊥ := ne_bot_of_gt h.lt

theorem eq_or_eq {X Y Z : Subgroup G} (h : IsChiefFactor X Y) (hZ : Z.Normal)
    (h₁ : Y ≤ Z) (h₂ : Z ≤ X) : Z = Y ∨ Z = X := by
  rcases eq_or_lt_of_le h₁ with h₁ | h₁
  · exact Or.inl h₁.symm
  rcases eq_or_lt_of_le h₂ with h₂ | h₂
  · exact Or.inr h₂
  exact absurd h₂ (h.not_lt_lt Z hZ h₁)

end IsChiefFactor

theorem exists_isChiefFactor [Finite G] (X : Subgroup G) [X.Normal] (hX : X ≠ ⊥) :
    ∃ Y : Subgroup G, IsChiefFactor X Y := by
  obtain ⟨Y, ⟨hY, hYX⟩, hmax⟩ :=
    exists_maximal_of_wellFoundedGT (fun Z : Subgroup G => Z.Normal ∧ Z < X)
      ⟨⊥, inferInstance, bot_lt_iff_ne_bot.2 hX⟩
  exact ⟨Y, inferInstance, hY, hYX, fun Z hZ h₁ h₂ => absurd (hmax ⟨hZ, h₂⟩ h₁.le) h₁.not_ge⟩

section Finite

variable [Finite G]

private theorem lowerCentralSeries_succ_lt (H : Subgroup G) [H.Normal]
    (h : ∀ X Y : Subgroup G, IsChiefFactor X Y → X ≤ H → ⁅H, X⁆ ≤ Y)
    (k : ℕ) (hk : H.lowerCentralSeries k ≠ ⊥) :
    H.lowerCentralSeries (k + 1) < H.lowerCentralSeries k := by
  obtain ⟨Y, hY⟩ := exists_isChiefFactor (H.lowerCentralSeries k) hk
  refine lt_of_le_of_lt ?_ hY.lt
  rw [H.lowerCentralSeries_succ, commutator_comm]
  exact h _ _ hY (H.lowerCentralSeries_le_self k)

private theorem lowerCentralSeries_eq_bot_aux (H : Subgroup G) [H.Normal]
    (h : ∀ X Y : Subgroup G, IsChiefFactor X Y → X ≤ H → ⁅H, X⁆ ≤ Y) :
    ∀ n k : ℕ, Nat.card (H.lowerCentralSeries k) ≤ n → H.lowerCentralSeries (k + n) = ⊥ := by
  intro n
  induction n with
  | zero => exact fun k hk => absurd hk (by simpa using Nat.card_pos.ne')
  | succ n ih =>
    intro k hk
    rcases eq_or_ne (H.lowerCentralSeries k) ⊥ with hb | hb
    · exact le_bot_iff.1 (hb ▸ H.lowerCentralSeries_antitone (Nat.le_add_right k (n + 1)))
    · have hlt := lowerCentralSeries_succ_lt H h k hb
      have hcard :
          Nat.card (H.lowerCentralSeries (k + 1)) < Nat.card (H.lowerCentralSeries k) := by
        have hss : ((H.lowerCentralSeries (k + 1) : Subgroup G) : Set G) ⊂
            ((H.lowerCentralSeries k : Subgroup G) : Set G) := by exact_mod_cast hlt
        exact Set.Finite.card_lt_card (Set.toFinite _) hss
      have := ih (k + 1) (by omega)
      rwa [show k + 1 + n = k + (n + 1) by omega] at this

theorem lowerCentralSeries_eq_bot_of_forall_isChiefFactor (H : Subgroup G) [H.Normal]
    (h : ∀ X Y : Subgroup G, IsChiefFactor X Y → X ≤ H → ⁅H, X⁆ ≤ Y) :
    H.lowerCentralSeries (Nat.card H) = ⊥ := by
  simpa using lowerCentralSeries_eq_bot_aux H h (Nat.card H) 0 (by simp)

theorem isNilpotent_of_forall_isChiefFactor (H : Subgroup G) [H.Normal]
    (h : ∀ X Y : Subgroup G, IsChiefFactor X Y → X ≤ H → ⁅H, X⁆ ≤ Y) :
    Group.IsNilpotent H :=
  Subgroup.isNilpotent_of_lowerCentralSeries_eq_bot
    (lowerCentralSeries_eq_bot_of_forall_isChiefFactor H h)

theorem exists_central_series_of_forall_isChiefFactor (H : Subgroup G) [H.Normal]
    (h : ∀ X Y : Subgroup G, IsChiefFactor X Y → X ≤ H → ⁅H, X⁆ ≤ Y) :
    ∃ (n : ℕ) (X : ℕ → Subgroup G), X 0 = ⊥ ∧ X n = H ∧ Monotone X ∧ (∀ i, (X i).Normal) ∧
      ∀ i, ⁅H, X (i + 1)⁆ ≤ X i := by
  refine ⟨Nat.card H, fun i => H.lowerCentralSeries (Nat.card H - i),
    by simpa using lowerCentralSeries_eq_bot_of_forall_isChiefFactor H h, by simp,
    fun i j hij => H.lowerCentralSeries_antitone (by omega), fun i => inferInstance, fun i => ?_⟩
  dsimp only
  rcases le_or_gt (Nat.card H) i with hi | hi
  · have h₁ : Nat.card H - i = 0 := by omega
    have h₂ : Nat.card H - (i + 1) = 0 := by omega
    rw [h₁, h₂, H.lowerCentralSeries_zero]
    exact (commutator_le_sup H H).trans (by simp)
  · have h₁ : Nat.card H - i = (Nat.card H - (i + 1)) + 1 := by omega
    rw [h₁, H.lowerCentralSeries_succ, commutator_comm]

end Finite

end CFSG.FeitThompson
