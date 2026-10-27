module

public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open scoped commutatorElement

theorem commutator_eq_bot_of_perfect_of_le {G : Type*} [Group G] {J O Q : Subgroup G}
    (hJ : ⁅J, J⁆ = J) (hQ : ⁅J, O⁆ ≤ Q) (hcent : ∀ q ∈ Q, ∀ j ∈ J, q * j = j * q) :
    ⁅J, O⁆ = ⊥ := by
  have h1 : ⁅⁅J, O⁆, J⁆ = ⊥ := by
    refine le_antisymm ?_ bot_le
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcent g₁ (hQ hg₁) g₂ hg₂
  have h2 : ⁅⁅O, J⁆, J⁆ = ⊥ := by rw [Subgroup.commutator_comm O J]; exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := J) (H₂ := J) (H₃ := O) h1 h2
  rwa [hJ] at h3

end CFSG.HardMathSupport.Solomon.Coordinator
