module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem eq_one_of_odd_orderOf_of_sq_mem {P : Subgroup G} (hP : IsPGroup 2 P) {g : G}
    (hodd : Odd (orderOf g)) (hg : g ^ 2 ∈ P) : g = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨g ^ 2, hg⟩
  have h : g ^ 2 ^ (k + 1) = 1 := by
    rw [pow_succ', pow_mul]
    simpa using congrArg Subtype.val hk
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.pow_right _ (Odd.coprime_two_right hodd)) (orderOf_dvd_of_pow_eq_one h))

theorem sq_mul_mem_iff_of_mul_inv_mem {N : Subgroup G} [N.Normal] {a b b' : G}
    (h : b' * b⁻¹ ∈ N) : (a * b') ^ 2 ∈ N ↔ (a * b) ^ 2 ∈ N := by
  have hb : (b' : G ⧸ N) = b := QuotientGroup.eq_iff_div_mem.mpr (by rwa [div_eq_mul_inv])
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow,
    QuotientGroup.mk_pow, QuotientGroup.mk_mul, QuotientGroup.mk_mul, hb]

end CFSG.GroupTheory
