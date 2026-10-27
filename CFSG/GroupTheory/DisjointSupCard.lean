module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.GroupTheory

theorem card_mul_card_le_card_sup_of_disjoint {G : Type*} [Group G] [Finite G]
    {H K : Subgroup G} (h : Disjoint H K) : Nat.card H * Nat.card K ≤ Nat.card ↥(H ⊔ K) := by
  let f : H × K → ↥(H ⊔ K) := fun p =>
    ⟨(p.1 : G) * p.2,
      Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Injective f := by
    intro p q hpq
    have h1 : (p.1 : G) * p.2 = (q.1 : G) * q.2 := congrArg Subtype.val hpq
    exact Subgroup.mul_injective_of_disjoint h h1
  calc Nat.card H * Nat.card K = Nat.card (H × K) := (Nat.card_prod H K).symm
    _ ≤ Nat.card ↥(H ⊔ K) := Nat.card_le_card_of_injective f hf

end CFSG.GroupTheory
