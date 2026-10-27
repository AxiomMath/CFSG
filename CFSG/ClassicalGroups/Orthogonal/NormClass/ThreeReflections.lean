module

public import CFSG.ClassicalGroups.Orthogonal.Derived

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem map_smul_add_smul (c d : K) (x a : V) :
    Q (c • x + d • a) = c ^ 2 * Q x + d ^ 2 * Q a + c * d * polar Q x a := by
  rw [QuadraticMap.map_add (Q : V → K), map_smul_eq_sq, map_smul_eq_sq,
    polar_smul_left_eq, polar_smul_right_eq]
  ring

private theorem polar_smul_add_polar_smul_sub_polar_smul_eq {x a : V} {s t : K} :
    polar Q x a • (s • x + t • a) + polar Q (s • x + t • a) a • x
        - polar Q x (s • x + t • a) • a
      = (2 * (s * polar Q x a + t * Q a)) • x + (-(2 * s * Q x)) • a := by
  rw [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_left_eq,
    polar_smul_right_eq, polar_smul_right_eq, polar_self_eq_two_mul, polar_self_eq_two_mul]
  module

theorem map_polar_smul_add_polar_smul_sub_polar_smul {x a w : V} {s t : K}
    (hw : w = s • x + t • a) :
    Q (polar Q x a • w + polar Q w a • x - polar Q x w • a) = 4 * Q x * Q a * Q w := by
  subst hw
  simp only [polar_smul_add_polar_smul_sub_polar_smul_eq, map_smul_add_smul]
  ring

theorem reflect_mul_reflect_mul_reflect_eq (h2 : (2 : K) ≠ 0) {x a w : V} {s t : K}
    (hw : w = s • x + t • a) (hx : Q x ≠ 0) (ha : Q a ≠ 0) (hw0 : Q w ≠ 0) :
    reflect Q x * reflect Q a * reflect Q w =
      reflect Q (polar Q x a • w + polar Q w a • x - polar Q x w • a) := by
  subst hw
  have hW : Q (s • x + t • a) = s ^ 2 * Q x + t ^ 2 * Q a + s * t * polar Q x a :=
    map_smul_add_smul s t x a
  have h4 : (4 : K) ≠ 0 := by
    have h : (4 : K) = 2 * 2 := by norm_num
    rw [h]
    exact mul_ne_zero h2 h2
  have hY : Q ((2 * (s * polar Q x a + t * Q a)) • x + (-(2 * s * Q x)) • a)
      = 4 * Q x * Q a * Q (s • x + t • a) := by
    rw [← polar_smul_add_polar_smul_sub_polar_smul_eq]
    rw [map_polar_smul_add_polar_smul_sub_polar_smul rfl]
  have hden : 4 * Q x * Q a * Q (s • x + t • a) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h4 hx) ha) hw0
  have hy : Q ((2 * (s * polar Q x a + t * Q a)) • x + (-(2 * s * Q x)) • a) ≠ 0 := by
    rw [hY]
    exact hden
  ext v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, reflect_apply hx, reflect_apply ha,
    reflect_apply hw0, polar_smul_add_polar_smul_sub_polar_smul_eq, reflect_apply hy, hY]
  simp only [polar_add_left, polar_add_right, polar_sub_right, polar_smul_left_eq,
    polar_smul_right_eq, polar_self_eq_two_mul, polar_comm Q a x, smul_add, smul_smul]
  match_scalars <;> field_simp <;> rw [hW] <;> ring

end CFSG.ClassicalGroups.Orthogonal

end
