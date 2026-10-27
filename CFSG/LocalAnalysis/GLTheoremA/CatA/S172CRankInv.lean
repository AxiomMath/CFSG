module

public import CFSG.ClassicalGroups.Orthogonal.Derived

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172C.Rank

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem commute_reflect_of_polar_eq_zero {a c : V} (h : polar Q a c = 0) :
    Commute (reflect Q a) (reflect Q c) := by
  have h1 := reflect_conj (reflect_mem_orthogonalGroup Q a) c
  rw [reflect_inv, reflect_apply_of_polar_eq_zero h] at h1
  have h2 := reflect_mul_self Q a
  calc reflect Q a * reflect Q c = reflect Q a * reflect Q c * (reflect Q a * reflect Q a) := by
        rw [h2, mul_one]
    _ = (reflect Q a * reflect Q c * reflect Q a) * reflect Q a := by simp only [mul_assoc]
    _ = reflect Q c * reflect Q a := by rw [h1]

theorem sq_reflect_mul_reflect {a c : V} (hac : polar Q a c = 0) :
    (reflect Q a * reflect Q c) ^ 2 = 1 := by
  rw [(commute_reflect_of_polar_eq_zero hac).mul_pow, pow_two, pow_two, reflect_mul_self,
    reflect_mul_self, one_mul]

theorem reflect_mul_reflect_conj_rot {a b c : V} (hac : polar Q a c = 0) (hbc : polar Q b c = 0) :
    reflect Q a * reflect Q c * (reflect Q a * reflect Q b) * (reflect Q a * reflect Q c)⁻¹ =
      (reflect Q a * reflect Q b)⁻¹ := by
  have h1 := commute_reflect_of_polar_eq_zero hac
  have h2 := commute_reflect_of_polar_eq_zero hbc
  have hcx : Commute (reflect Q c) (reflect Q a * reflect Q b) := h1.symm.mul_right h2.symm
  have hconj : reflect Q c * (reflect Q a * reflect Q b) * (reflect Q c)⁻¹ =
      reflect Q a * reflect Q b := by
    rw [hcx.eq, mul_assoc, mul_inv_cancel, mul_one]
  calc reflect Q a * reflect Q c * (reflect Q a * reflect Q b) * (reflect Q a * reflect Q c)⁻¹
      = reflect Q a * (reflect Q c * (reflect Q a * reflect Q b) * (reflect Q c)⁻¹) *
          (reflect Q a)⁻¹ := by group
    _ = reflect Q a * (reflect Q a * reflect Q b) * (reflect Q a)⁻¹ := by rw [hconj]
    _ = (reflect Q a * reflect Q b)⁻¹ := by
        rw [mul_inv_rev, reflect_inv, reflect_inv]
        simp only [← mul_assoc, reflect_mul_self, one_mul]

theorem commute_reflect_mul_reflect_rot {a c a' b' : V} (h1 : polar Q a a' = 0)
    (h2 : polar Q a b' = 0) (h3 : polar Q c a' = 0) (h4 : polar Q c b' = 0) :
    Commute (reflect Q a * reflect Q c) (reflect Q a' * reflect Q b') :=
  Commute.mul_left
    (Commute.mul_right (commute_reflect_of_polar_eq_zero h1) (commute_reflect_of_polar_eq_zero h2))
    (Commute.mul_right (commute_reflect_of_polar_eq_zero h3) (commute_reflect_of_polar_eq_zero h4))

theorem reflect_mul_reflect_apply_of_polar_eq_zero {a b u : V} (ha : polar Q a u = 0)
    (hb : polar Q b u = 0) : (reflect Q a * reflect Q b) u = u := by
  rw [LinearEquiv.mul_apply, reflect_apply_of_polar_eq_zero hb, reflect_apply_of_polar_eq_zero ha]

theorem reflect_mul_reflect_apply_ne [CharP F 2] {x y : V} (hx : Q x ≠ 0) (hy : Q y ≠ 0)
    (hxy : polar Q x y ≠ 0) : (reflect Q x * reflect Q y) x ≠ x := by
  have hxx : polar Q x x = 0 := by rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]
  intro h
  rw [LinearEquiv.mul_apply, reflect_apply hy, map_sub, map_smul, reflect_apply hx x,
    reflect_apply hx y, hxx, zero_div, zero_smul, sub_zero] at h
  have h1 : (polar Q y x / Q y) • (y - (polar Q x y / Q x) • x) = 0 := sub_eq_self.1 h
  have hc : polar Q y x / Q y ≠ 0 := div_ne_zero (by rw [polar_comm]; exact hxy) hy
  have h2 : y - (polar Q x y / Q x) • x = 0 := (smul_eq_zero.1 h1).resolve_left hc
  have h3 : y = (polar Q x y / Q x) • x := sub_eq_zero.1 h2
  apply hxy
  rw [h3, polar_smul_right_eq, hxx, mul_zero]

theorem polar_ne_zero_of_orderOf_reflect_mul_reflect {x y : V} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hord : orderOf (reflect Q x * reflect Q y) = p) : polar Q x y ≠ 0 := by
  intro h
  have h1 : p ∣ 2 := hord ▸ orderOf_dvd_of_pow_eq_one (sq_reflect_mul_reflect h)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1)

end CFSG.LocalAnalysis.GLTheoremA.S172C.Rank

end
