module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG

theorem card_mul_card_le_of_inf_eq_bot {G : Type*} [Group G] {A D D' : Subgroup G}
    [Finite A] (hD : D ≤ A) (hD' : D' ≤ A) (hDD' : D ⊓ D' = ⊥) :
    Nat.card D * Nat.card D' ≤ Nat.card A := by
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective
    (fun p : D × D' => (⟨p.1 * p.2, A.mul_mem (hD p.1.2) (hD' p.2.2)⟩ : A))
    fun p q h =>
      Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hDD') (congrArg Subtype.val h)

end CFSG
