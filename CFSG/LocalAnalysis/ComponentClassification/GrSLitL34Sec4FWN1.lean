module

public import CFSG.GroupTheory.ThompsonIndexTwo

public section

namespace CFSG.ComponentClassification.GrSLit.FW

variable {X : Type*} [Group X] [Finite X]

theorem exists_conj_mem_of_least_order [IsSimpleGroup X] (hnab : ∃ g h : X, g * h ≠ h * g)
    {T U : Subgroup X} (hT : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index) (hUT : U ≤ T)
    (hUidx : U.relIndex T = 2) {v : X} (hvT : v ∈ T) (hvU : v ∉ U)
    (hmin : ∀ y ∈ T, y ∉ U → orderOf v ≤ orderOf y) : ∃ g : X, g⁻¹ * v * g ∈ U := by
  by_contra hno
  push Not at hno
  obtain ⟨N, hN, hidx⟩ :=
    ThompsonIndexTwo.exists_normal_index_two_of_thompson hT hTidx hUT hUidx hvT hvU hmin hno
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with rfl | rfl
  · rw [Subgroup.index_bot] at hidx
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic X := isCyclic_of_prime_card hidx
    obtain ⟨g, h, hgh⟩ := hnab
    exact hgh ((IsCyclic.isMulCommutative (α := X)).is_comm.comm g h)
  · rw [Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)

end CFSG.ComponentClassification.GrSLit.FW
