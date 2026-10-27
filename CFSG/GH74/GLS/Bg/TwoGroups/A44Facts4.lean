module

public import CFSG.GH74.GLS.Bg.TwoGroups.A44Data

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace A44

theorem S4_inj1 : ∀ x ∈ S4list1, (∀ j : Fin 4, act4 x j = j) → x = M4.one := by decide +kernel

theorem S4_inj2 : ∀ x ∈ S4list2, (∀ j : Fin 4, act4 x j = j) → x = M4.one := by decide +kernel

theorem card_S4_1 : Fintype.card {x : G96 // x.1 ∈ S4list1} = 24 := by decide +kernel

theorem card_S4_2 : Fintype.card {x : G96 // x.1 ∈ S4list2} = 24 := by decide +kernel

theorem S4_gen : ∀ a b : G96, M4.mul (M4.sq a.1) (M4.sq a.1) = M4.one → M4.sq a.1 ≠ M4.one →
    b.1 ≠ M4.one → M4.mul b.1 b.1 = M4.one → M4.mul (M4.sq (M4.mul a.1 b.1)) (M4.mul a.1 b.1) = M4.one →
    M4.mul a.1 b.1 ≠ M4.one →
    (a.1 ∈ S4list1 ∧ b.1 ∈ S4list1) ∨ (a.1 ∈ S4list2 ∧ b.1 ∈ S4list2) := by decide +kernel

theorem S4_swap : ∀ y ∈ [dd, M4.mul dd iota], ∀ k : M4, k.IsInv →
    ((M4.mul (M4.mul y k) y ∈ S4list1 ↔ k ∈ S4list2) ∧
      (M4.mul (M4.mul y k) y ∈ S4list2 ↔ k ∈ S4list1)) := by
  decide +kernel

theorem S4_distinct : ∃ x ∈ S4list1, x ∉ S4list2 := by decide +kernel

end A44

end CFSG.GH74.GLS.Bg.TwoGroups
