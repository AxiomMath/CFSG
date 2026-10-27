module

public import CFSG.CharacterTheory.Burnside.GroupEndgame

public section

namespace CFSG

namespace Burnside.UniverseReduction

universe u

theorem isSolvable_of_small_simple_case
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (small_simple_case :
      ∀ (H : Type) [Group H] [Fintype H] (c e : ℕ),
        Nat.card H = p ^ c * q ^ e →
        IsSimpleGroup H → Group.IsSolvable H) :
    ∀ (G : Type u) [Group G] [Fintype G] (a b : ℕ),
      Nat.card G = p ^ a * q ^ b → Group.IsSolvable G := by
  apply
    Burnside.GroupEndgame.isSolvable_of_card_eq_prime_pow_mul_prime_pow_of_simple_case
      hp hq
  intro H _ _ c e hcard hsimple
  obtain ⟨H', groupH', fintypeH', ⟨equivH⟩⟩ :=
    Finite.exists_type_univ_nonempty_mulEquiv.{u, 0} H
  let : Group H' := groupH'
  let : Fintype H' := fintypeH'
  have hcard' : Nat.card H' = p ^ c * q ^ e :=
    (Nat.card_congr equivH.toEquiv).symm.trans hcard
  have hsimple' : IsSimpleGroup H' :=
    equivH.isSimpleGroup_congr.mp hsimple
  have hsolvable' : Group.IsSolvable H' :=
    small_simple_case H' c e hcard' hsimple'
  let : Group.IsSolvable H' := hsolvable'
  exact Group.isSolvable_of_surjective
    (f := equivH.symm.toMonoidHom) equivH.symm.surjective

end Burnside.UniverseReduction

end CFSG
