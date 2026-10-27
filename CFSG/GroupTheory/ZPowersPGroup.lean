module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GroupTheory

theorem isPGroup_zpowers_of_sq_eq_one {H : Type*} [Group H] {x : H} (hx : x ^ 2 = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  rintro ⟨g, hg⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

end CFSG.GroupTheory
