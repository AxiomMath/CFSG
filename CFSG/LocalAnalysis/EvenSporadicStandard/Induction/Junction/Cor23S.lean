module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chains

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

@[expose] def Cor23SAt (H : Type) [Group H] [Finite H] : Prop :=
  CFSG.Assembly.KProper CFSG.Blueprint.Catalog H →
  ∀ N : Subgroup H, FStarSimple N → (∀ P : Subgroup H, ⁅P, P⁆ = P → P ≤ N) →
    ∀ T₀ K : Subgroup H, IsPGroup 2 T₀ → IsCompIn K (centralizer (T₀ : Set H)) →
      ¬ Nonempty ((↥K ⧸ center ↥K) ≃* alternatingGroup (Fin 7)) →
      (¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.LieModel (↥K ⧸ center ↥K) .PSL 2 p f) →
        ∃ (n : ℕ) (L T : ℕ → Subgroup H) (s : ℕ → H), Sol78Chain23 H N n L T s ∧ L 0 = K

theorem perfect_le_of_index_le_two {H : Type} [Group H] [Finite H] {N : Subgroup H}
    (hNn : N.Normal) (hN : N.index ≤ 2) {P : Subgroup H} (hP : ⁅P, P⁆ = P) : P ≤ N := by
  have := hNn
  have hcard : Nat.card (H ⧸ N) ≤ 2 := hN
  have hpos : 0 < Nat.card (H ⧸ N) := Nat.card_pos
  have hcomm : ∀ a b : H ⧸ N, a * b = b * a := by
    rcases Nat.lt_or_ge (Nat.card (H ⧸ N)) 2 with h | h
    · have h1 : Nat.card (H ⧸ N) = 1 := by omega
      have := (Nat.card_eq_one_iff_unique.1 h1).1
      intro a b
      exact Subsingleton.elim _ _
    · have h2 : Nat.card (H ⧸ N) = 2 := by omega
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hcyc : IsCyclic (H ⧸ N) := isCyclic_of_prime_card h2
      exact fun a b => (IsCyclic.commGroup (α := H ⧸ N)).mul_comm a b
  intro x hx
  have h1 : ⁅P.map (QuotientGroup.mk' N), P.map (QuotientGroup.mk' N)⁆ = ⊥ := by
    rw [eq_bot_iff, commutator_le]
    intro a _ b _
    refine Subgroup.mem_bot.2 ?_
    rw [commutatorElement_def, hcomm a b]
    group
  rw [← Subgroup.map_commutator, hP] at h1
  have : QuotientGroup.mk' N x ∈ (⊥ : Subgroup (H ⧸ N)) := h1 ▸ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  exact this

theorem perfect_subgroups_le_of_index_le_two {H : Type} [Group H] [Finite H] {N : Subgroup H}
    (hNn : N.Normal) (hN : N.index ≤ 2) : ∀ P : Subgroup H, ⁅P, P⁆ = P → P ≤ N :=
  fun _ hP => perfect_le_of_index_le_two hNn hN hP

end CFSG.EvenSporadicStandard.Induction
