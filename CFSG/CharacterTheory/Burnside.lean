module

public import CFSG.CharacterTheory.Burnside.CharacterObstruction
public import CFSG.CharacterTheory.Burnside.UniverseReduction

public section

namespace CFSG

namespace Burnside

theorem finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow {G : Type*} [Group G] [Fintype G]
    {p q a b : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hpq : p ≠ q)
    (hcard : Fintype.card G = p ^ a * q ^ b) :
    Group.IsSolvable G := by
  have hsmall :
      ∀ (H : Type) [Group H] [Fintype H] (c e : ℕ),
        Nat.card H = p ^ c * q ^ e → Group.IsSolvable H := by
    apply
      Burnside.GroupEndgame.isSolvable_of_card_eq_prime_pow_mul_prime_pow_of_no_prime_pow_conjClass
        hp hq
    intro H _ _ hsimple hnoncomm x hx r k hr
    let : IsSimpleGroup H := hsimple
    exact Burnside.CharacterObstruction.no_prime_pow_conjClass
      hnoncomm x hx r k hr
  refine Burnside.UniverseReduction.isSolvable_of_small_simple_case
    hp hq ?_ G a b ?_
  · intro H _ _ c e hHcard _
    exact hsmall H c e hHcard
  · simpa [Nat.card_eq_fintype_card] using hcard

end Burnside

end CFSG
