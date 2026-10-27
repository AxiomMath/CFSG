module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

open MulAction

theorem exists_ne_fixed_of_two_group {G α : Type*} [Group G] [MulAction G α] [Finite α]
    (hG : IsPGroup 2 G) (hα : Even (Nat.card α)) {a : α}
    (ha : a ∈ fixedPoints G α) :
    ∃ b ∈ fixedPoints G α, b ≠ a := by
  have hc : Nat.card α % 2 = Nat.card (fixedPoints G α) % 2 :=
    hG.card_modEq_card_fixedPoints α
  have hF0 : Nat.card (fixedPoints G α) % 2 = 0 := by
    have := Nat.even_iff.mp hα
    omega
  have hFpos : 0 < Nat.card (fixedPoints G α) := by
    have : Nonempty (fixedPoints G α) := ⟨⟨a, ha⟩⟩
    exact Nat.card_pos
  by_contra h
  have hfix : ∀ x : fixedPoints G α, (x : α) = a := fun x => by
    by_contra hx
    exact h ⟨x, x.2, hx⟩
  have hsub : Subsingleton (fixedPoints G α) :=
    ⟨fun x y => Subtype.ext ((hfix x).trans (hfix y).symm)⟩
  have hle : Nat.card (fixedPoints G α) ≤ 1 :=
    Finite.card_le_one_iff_subsingleton.mpr hsub
  omega

end CFSG.AGLEmbeddingD2.Wilson.Proving

end
