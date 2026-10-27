module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

public section

namespace CFSG

theorem sq_eq_one_of_mem_zpowers {G : Type*} [Group G] {x y : G} (hx : x ^ 2 = 1)
    (hy : y ∈ Subgroup.zpowers x) : y ^ 2 = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

end CFSG

end
