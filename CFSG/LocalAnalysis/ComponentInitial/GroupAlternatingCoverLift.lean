module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.ComponentInitial

variable {P Q : Type*} [Group P] [Group Q] {η : P →* Q}

theorem coprime_two_three : Nat.Coprime 2 3 := by norm_num

theorem eq_one_of_pow_three_eq_one_of_isPGroup {G : Type*} [Group G] (hG : IsPGroup 2 G) {k : G}
    (hk : k ^ 3 = 1) : k = 1 :=
  orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (hG.orderOf_coprime coprime_two_three k)
    (orderOf_dvd_of_pow_eq_one hk))

theorem exists_lift_pow_three_eq_one (hK : η.ker ≤ Subgroup.center P) (hK2 : IsPGroup 2 η.ker)
    {y : P} (hy : η y ^ 3 = 1) : ∃ x, η x = η y ∧ x ^ 3 = 1 := by
  have hy3 : y ^ 3 ∈ η.ker := by rw [MonoidHom.mem_ker, map_pow, hy]
  set k : η.ker := (hK2.powEquiv coprime_two_three).symm ⟨y ^ 3, hy3⟩⁻¹ with hk
  have hk3 : (k : P) ^ 3 = (y ^ 3)⁻¹ := by
    have h := (hK2.powEquiv coprime_two_three).apply_symm_apply ⟨y ^ 3, hy3⟩⁻¹
    rw [IsPGroup.powEquiv_apply, ← hk] at h
    exact congrArg Subtype.val h
  have hkc : Commute y k := Subgroup.mem_center_iff.mp (hK k.2) y
  refine ⟨y * k, ?_, ?_⟩
  · rw [map_mul, MonoidHom.mem_ker.mp k.2, mul_one]
  · rw [hkc.mul_pow, hk3, mul_inv_cancel]

theorem eq_of_pow_three_eq_one_of_map_eq (hK : η.ker ≤ Subgroup.center P)
    (hK2 : IsPGroup 2 η.ker) {x x' : P} (hx : x ^ 3 = 1) (hx' : x' ^ 3 = 1) (h : η x = η x') :
    x = x' := by
  have hk : x⁻¹ * x' ∈ η.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hkc : Commute x (x⁻¹ * x') := Subgroup.mem_center_iff.mp (hK hk) x
  have hk3 : (x⁻¹ * x') ^ 3 = 1 := by
    have h' : x' = x * (x⁻¹ * x') := by rw [mul_inv_cancel_left]
    rw [h', hkc.mul_pow, hx, one_mul] at hx'
    exact hx'
  have h1 : (⟨x⁻¹ * x', hk⟩ : η.ker) = 1 :=
    eq_one_of_pow_three_eq_one_of_isPGroup hK2 (Subtype.ext (by simpa using hk3))
  have h2 : x⁻¹ * x' = 1 := congrArg Subtype.val h1
  exact (inv_mul_eq_one.mp h2)

end CFSG.LocalAnalysis.ComponentInitial
