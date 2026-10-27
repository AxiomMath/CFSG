module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open MulAction

variable {G X : Type*} [Group G] [MulAction G X]

def stabilizerSubgroupEquiv (H : Subgroup G) (x : X) :
    ↥(H ⊓ stabilizer G x) ≃ stabilizer H x where
  toFun y := ⟨⟨y.1, y.2.1⟩, y.2.2⟩
  invFun z := ⟨z.1.1, z.1.2, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem natCard_eq_ncard_orbit_mul (H : Subgroup G) (x : X) :
    Nat.card H = (orbit H x).ncard * Nat.card ↥(H ⊓ stabilizer G x) := by
  rw [Nat.card_congr (stabilizerSubgroupEquiv H x), ← index_stabilizer H x, mul_comm,
    Subgroup.card_mul_index]

theorem card_le_mul_card_inf_stabilizer (H : Subgroup G) (x : X) (S : Finset X)
    (h : ∀ g ∈ H, g • x ∈ S) : Nat.card H ≤ S.card * Nat.card ↥(H ⊓ stabilizer G x) := by
  rw [natCard_eq_ncard_orbit_mul H x]
  refine Nat.mul_le_mul_right _ ?_
  have hsub : orbit H x ⊆ (S : Set X) := by
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    exact h g hg
  exact (Set.ncard_le_ncard hsub S.finite_toSet).trans_eq (Set.ncard_coe_finset S)

end CFSG.EvenSporadicStandard.TwoFi22.DS81
