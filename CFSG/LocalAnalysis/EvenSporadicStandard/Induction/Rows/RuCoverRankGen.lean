module

public import CFSG.RankThree.PartTwo.Census.TransitiveLift

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.RankThree.PartTwo.Sec4.Census
open scoped commutatorElement

theorem three_le_pRank_of_isotropic {J X : Type} [Group J] [Finite J] [Group X] {φ : J →* X}
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center J) {W : Subgroup X}
    (hW2 : ∀ x ∈ W, x ^ 2 = 1) (hW8 : 8 ≤ Nat.card W) {e₀ : X}
    (htr : ∀ x ∈ W, x ≠ 1 → ∃ g : X, g * e₀ * g⁻¹ = x)
    (hcomm : ∀ y y' : J, φ y ∈ W → φ y' ∈ W → y * y' = y' * y) : 3 ≤ CFSG.pRank 2 J := by
  have hsq : ∀ y : J, φ y ∈ W → ∃ c : J, φ c = 1 ∧ y ^ 2 = c ^ 2 := fun y hy =>
    TransitiveLift.exists_sq_eq_sq hφ hker hW2 hW8 htr hy
  obtain ⟨A, hA, hAcard⟩ := TransitiveLift.exists_isElementaryAbelian_card hφ hker hcomm hsq
  refine TransitiveLift.le_pRank_of_card hA (k := 3) ?_
  rw [hAcard]
  have : Nonempty {c : J // φ c = 1 ∧ c ^ 2 = 1} := ⟨⟨1, map_one φ, one_pow 2⟩⟩
  have hpos : 0 < Nat.card {c : J // φ c = 1 ∧ c ^ 2 = 1} := Nat.card_pos
  calc 2 ^ 3 = 8 := by norm_num
    _ ≤ Nat.card W := hW8
    _ = Nat.card W * 1 := (mul_one _).symm
    _ ≤ _ := Nat.mul_le_mul_left _ hpos

end CFSG.EvenSporadicStandard.Induction
