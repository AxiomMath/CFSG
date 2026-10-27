module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

theorem card_normalizer_mul_card_eq {M : Type*} [Group M] [Finite M] {p : ℕ} [Fact p.Prime]
    {K : Subgroup M} [K.Normal] (P : Sylow p K) :
    Nat.card (Subgroup.normalizer (((P : Subgroup K).map K.subtype : Subgroup M) : Set M)) *
        Nat.card K =
      Nat.card M * Nat.card (K ⊓ Subgroup.normalizer
        (((P : Subgroup K).map K.subtype : Subgroup M) : Set M) : Subgroup M) := by
  set N : Subgroup M :=
    Subgroup.normalizer (((P : Subgroup K).map K.subtype : Subgroup M) : Set M) with hN
  have hfr : N ⊔ K = ⊤ := Sylow.normalizer_sup_eq_top (N := K) P
  have h1 : K.relIndex ⊤ = K.relIndex N := by
    rw [← hfr, Subgroup.relIndex_sup_right]
  have hA := Subgroup.relIndex_mul_card (H := K) (K := ⊤)
  have hB := Subgroup.relIndex_mul_card (H := K) (K := N)
  rw [inf_top_eq, Subgroup.card_top] at hA
  rw [← hB, ← hA, h1]
  ring

end CFSG.AGLEmbeddingD2.Wilson.Proving
