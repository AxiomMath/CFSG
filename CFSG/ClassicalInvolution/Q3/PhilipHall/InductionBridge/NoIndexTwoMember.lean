module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

open scoped MatrixGroups

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge

open CFSG.Open

theorem sl2Three_no_index_two (H : Subgroup SL(2, ZMod 3)) : H.index ≠ 2 := by
  intro h
  have : H.Normal := Subgroup.normal_of_index_eq_two h
  have key : ∀ g : SL(2, ZMod 3), ∃ a b : SL(2, ZMod 3), g = a ^ 2 * b ^ 2 := by decide +kernel
  have hsq : ∀ a : SL(2, ZMod 3), a ^ 2 ∈ H := fun a => by
    have := Subgroup.pow_index_mem H a
    rwa [h] at this
  have htop : H = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨a, b, rfl⟩ := key g
    exact H.mul_mem (hsq a) (hsq b)
  rw [htop, Subgroup.index_top] at h
  exact absurd h (by norm_num)

end CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge
