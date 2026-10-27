module

public import CFSG.CharacterTheory.FrobeniusKernel.Frobenius

public section

namespace CFSG

namespace FrobeniusKernel

theorem frobenius_kernel_isNormal (G X : Type) [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : 2 ≤ Fintype.card X)
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (hstab : ∀ x : X, MulAction.stabilizer G x ≠ ⊥)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y) :
    ∃ N : Subgroup G, N.Normal ∧
      (N : Set G) = {1} ∪ {g : G | ∀ x : X, g • x ≠ x} := by
  exact Frobenius.frobenius_kernel_isNormal
    G X hcard htrans hstab hfrob

end FrobeniusKernel

end CFSG
