module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.GroupActions

open MulAction

theorem fixed_point_centralizer_order_bound {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω]
    [Finite Ω] (z : G) (a : Ω) (ha : z • a = a) :
    Nat.card (Subgroup.centralizer {z} : Subgroup G) ≤
      Nat.card {x : Ω | z • x = x} *
        Nat.card (Subgroup.centralizer {z} ⊓ stabilizer G a : Subgroup G) := by
  set C := Subgroup.centralizer ({z} : Set G) with hC
  have hcomm : ∀ c ∈ C, c * z = z * c := fun c hc =>
    Subgroup.mem_centralizer_singleton_iff.1 hc
  have h1 : Nat.card C = Nat.card (orbit C a) * Nat.card (stabilizer C a) := by
    rw [← Nat.card_prod, Nat.card_congr (orbitProdStabilizerEquivGroup C a)]
  have h2 : Nat.card (orbit C a) ≤ Nat.card {x : Ω | z • x = x} := by
    refine Nat.card_mono (Set.toFinite _) ?_
    rintro _ ⟨c, rfl⟩
    change z • ((c : G) • a) = (c : G) • a
    rw [← mul_smul, ← hcomm c c.2, mul_smul, ha]
  have h3 : Nat.card (stabilizer C a) = Nat.card (C ⊓ stabilizer G a : Subgroup G) :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [h1, h3]
  exact Nat.mul_le_mul_right _ h2

end CFSG.GroupActions
