module

public import Mathlib.GroupTheory.Frattini

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {p : ℕ} {P : Type*} [Group P]

structure IsExtraspecial (p : ℕ) (P : Type*) [Group P] : Prop where
  prime : p.Prime
  finite : Finite P
  isPGroup : IsPGroup p P
  center_eq_commutator : Subgroup.center P = commutator P
  commutator_eq_frattini : commutator P = frattini P
  card_center : Nat.card (Subgroup.center P) = p

namespace IsExtraspecial

theorem center_eq_frattini (h : IsExtraspecial p P) : Subgroup.center P = frattini P :=
  h.center_eq_commutator.trans h.commutator_eq_frattini

theorem card_commutator (h : IsExtraspecial p P) : Nat.card (commutator P) = p := by
  rw [← h.center_eq_commutator]; exact h.card_center

theorem card_frattini (h : IsExtraspecial p P) : Nat.card (frattini P) = p := by
  rw [← h.center_eq_frattini]; exact h.card_center

theorem center_ne_bot (h : IsExtraspecial p P) : Subgroup.center P ≠ ⊥ := by
  intro hc
  rw [Subgroup.eq_bot_iff_card, h.card_center] at hc
  exact h.prime.one_lt.ne' hc

theorem commutator_ne_bot (h : IsExtraspecial p P) : commutator P ≠ ⊥ :=
  h.center_eq_commutator ▸ h.center_ne_bot

theorem frattini_ne_bot (h : IsExtraspecial p P) : frattini P ≠ ⊥ :=
  h.center_eq_frattini ▸ h.center_ne_bot

theorem not_isMulCommutative (h : IsExtraspecial p P) : ¬ IsMulCommutative P := fun hc =>
  h.commutator_ne_bot ((commutator_eq_bot_iff P).2 hc)

theorem center_ne_top (h : IsExtraspecial p P) : Subgroup.center P ≠ ⊤ := fun hc =>
  h.not_isMulCommutative (Subgroup.center_eq_top_iff.1 hc)

theorem nontrivial (h : IsExtraspecial p P) : Nontrivial P := by
  refine not_subsingleton_iff_nontrivial.1 fun hs => h.not_isMulCommutative ?_
  exact ⟨⟨fun a b => by rw [Subsingleton.elim a b]⟩⟩

theorem isCyclic_center (h : IsExtraspecial p P) : IsCyclic (Subgroup.center P) :=
  haveI := Fact.mk h.prime
  isCyclic_of_prime_card h.card_center

theorem isMulCommutative_quotient_center (h : IsExtraspecial p P) :
    IsMulCommutative (P ⧸ Subgroup.center P) :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.2 h.center_eq_commutator.ge

theorem exists_card_eq_pow (h : IsExtraspecial p P) : ∃ n, Nat.card P = p ^ n :=
  haveI := h.finite
  haveI := Fact.mk h.prime
  h.isPGroup.exists_card_eq

end IsExtraspecial

end

end CFSG.FeitThompson
