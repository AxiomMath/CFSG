module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalElementary
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] noncomputable def shortWeyl (P : HypPair Q) (a : V) : V ≃ₗ[K] V :=
  eichler Q P.e a * eichler Q P.f ((Q a)⁻¹ • a) * eichler Q P.e a

theorem shortWeyl_mem (P : HypPair Q) (a : V) : shortWeyl P a ∈ orthElementaryGroup Q :=
  mul_mem (mul_mem (eichler_mem_elementaryGroup Q _ _) (eichler_mem_elementaryGroup Q _ _))
    (eichler_mem_elementaryGroup Q _ _)

section Apply

variable (P : HypPair Q) {a : V} (ha : a ∈ P.perp) (hd : Q a ≠ 0)
include ha hd

omit ha hd in
theorem shortWeyl_apply (x : V) :
    shortWeyl P a x = eichler Q P.e a (eichler Q P.f ((Q a)⁻¹ • a) (eichler Q P.e a x)) :=
  rfl

omit hd in
theorem polar_e_a : polar Q P.e a = 0 := (HypPair.mem_perp.1 ha).1

omit hd in
theorem polar_f_a : polar Q P.f a = 0 := (HypPair.mem_perp.1 ha).2

omit hd in
theorem eichler_e_a_apply (x : V) :
    eichler Q P.e a x = x + polar Q x P.e • a - (polar Q x a + Q a * polar Q x P.e) • P.e :=
  eichler_apply P.Q_e (polar_e_a P ha) x

omit hd in
theorem eichler_f_a_apply (c : K) (x : V) :
    eichler Q P.f (c • a) x =
      x + polar Q x P.f • (c • a) - (c * polar Q x a + c ^ 2 * Q a * polar Q x P.f) • P.f := by
  rw [eichler_apply P.Q_f (by rw [polar_smul_right_eq, polar_f_a P ha, mul_zero]),
    polar_smul_right_eq, map_smul_eq_sq]

omit hd in
theorem eichler_e_a_f : eichler Q P.e a P.f = P.f + a - Q a • P.e := by
  rw [eichler_e_a_apply P ha, P.polar_fe, polar_f_a P ha]
  module

omit hd in
theorem eichler_e_a_a : eichler Q P.e a a = a - (2 * Q a) • P.e := by
  rw [eichler_e_a_apply P ha, polar_comm, polar_e_a P ha, polar_self_eq_two_mul]
  module

omit hd in
theorem eichler_e_a_perp {z : V} (hz : z ∈ P.perp) :
    eichler Q P.e a z = z - polar Q z a • P.e := by
  rw [eichler_e_a_apply P ha, polar_comm, (HypPair.mem_perp.1 hz).1]
  module

theorem eichler_f_a_e :
    eichler Q P.f ((Q a)⁻¹ • a) P.e = P.e + (Q a)⁻¹ • a - (Q a)⁻¹ • P.f := by
  rw [eichler_f_a_apply P ha, P.polar_ef, polar_e_a P ha, mul_zero, zero_add]
  match_scalars <;> field_simp

omit ha hd in
theorem eichler_f_a_f : eichler Q P.f ((Q a)⁻¹ • a) P.f = P.f := eichler_apply_self _ _

theorem eichler_f_a_a : eichler Q P.f ((Q a)⁻¹ • a) a = a - (2 : K) • P.f := by
  rw [eichler_f_a_apply P ha, polar_comm, polar_f_a P ha, polar_self_eq_two_mul]
  match_scalars <;> field_simp <;> ring

omit hd in
theorem eichler_f_a_perp {z : V} (hz : z ∈ P.perp) :
    eichler Q P.f ((Q a)⁻¹ • a) z = z - ((Q a)⁻¹ * polar Q z a) • P.f := by
  rw [eichler_f_a_apply P ha, polar_comm, (HypPair.mem_perp.1 hz).2]
  module

theorem shortWeyl_e : shortWeyl P a P.e = -(Q a)⁻¹ • P.f := by
  simp only [shortWeyl_apply, eichler_apply_self, eichler_f_a_e P ha hd, map_sub, map_add,
    map_smul, eichler_e_a_a P ha, eichler_e_a_f P ha]
  match_scalars <;> field_simp <;> ring

theorem shortWeyl_f : shortWeyl P a P.f = -(Q a) • P.e := by
  simp only [shortWeyl_apply, eichler_e_a_f P ha, map_sub, map_add, map_smul, eichler_apply_self,
    eichler_f_a_a P ha hd, eichler_f_a_e P ha hd, eichler_e_a_a P ha]
  match_scalars <;> field_simp <;> ring

theorem shortWeyl_perp {z : V} (hz : z ∈ P.perp) :
    shortWeyl P a z = z - (polar Q z a * (Q a)⁻¹) • a := by
  simp only [shortWeyl_apply, eichler_e_a_perp P ha hz, map_sub, map_add, map_smul,
    eichler_f_a_perp P ha hz, eichler_f_a_e P ha hd, eichler_apply_self, eichler_e_a_a P ha,
    eichler_e_a_f P ha]
  match_scalars <;> field_simp <;> ring

theorem shortWeyl_self : shortWeyl P a a = -a := by
  rw [shortWeyl_perp P ha hd ha, polar_self_eq_two_mul, mul_assoc, mul_inv_cancel₀ hd, mul_one,
    two_smul, sub_add_cancel_left]

theorem shortWeyl_mul_self : shortWeyl P a * shortWeyl P a = 1 := by
  have hperp : ∀ z ∈ P.perp, shortWeyl P a (shortWeyl P a z) = z := by
    intro z hz
    rw [shortWeyl_perp P ha hd hz, map_sub, map_smul, shortWeyl_perp P ha hd hz,
      shortWeyl_self P ha hd, smul_neg, sub_neg_eq_add, sub_add_cancel]
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq]
  conv_rhs => rw [P.eq_add_proj x]
  conv_lhs => rw [P.eq_add_proj x]
  rw [map_add, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
    shortWeyl_e P ha hd, shortWeyl_f P ha hd, map_smul, map_smul, shortWeyl_e P ha hd,
    shortWeyl_f P ha hd, hperp _ (P.proj_mem_perp x)]
  match_scalars <;> field_simp

end Apply


theorem orthogonal_geometry_tail_short_root_Weyl_element (P : HypPair Q) {a : V}
    (ha : a ∈ P.perp) (hd : Q a ≠ 0) :
    shortWeyl P a = eichler Q P.e a * eichler Q P.f ((Q a)⁻¹ • a) * eichler Q P.e a ∧
      shortWeyl P a ∈ orthElementaryGroup Q ∧
      shortWeyl P a P.e = -(Q a)⁻¹ • P.f ∧ shortWeyl P a P.f = -(Q a) • P.e ∧
      (∀ z ∈ P.perp, shortWeyl P a z = z - (polar Q z a * (Q a)⁻¹) • a) ∧
      shortWeyl P a * shortWeyl P a = 1 :=
  ⟨rfl, shortWeyl_mem P a, shortWeyl_e P ha hd, shortWeyl_f P ha hd,
    fun _ hz => shortWeyl_perp P ha hd hz, shortWeyl_mul_self P ha hd⟩

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
