module

public import CFSG.ClassicalGroups.Orthogonal.CharTwoTransvection
public import Mathlib
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

section Basic

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem vec_add_self (w : V) : w + w = 0 := by
  have h : ((1 : ZMod 2) + 1) • w = 0 := by
    rw [show ((1 : ZMod 2) + 1) = 0 from rfl, zero_smul]
  rwa [add_smul, one_smul] at h

theorem vec_neg (w : V) : -w = w := neg_eq_of_add_eq_zero_right (vec_add_self w)

theorem zmod_two_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

variable (Q : QuadraticForm (ZMod 2) V)

theorem polar_self_zero (x : V) : polar Q x x = 0 := by
  rw [QuadraticMap.polar_self]
  generalize Q x = c
  revert c
  decide

theorem map_add_polar (x y : V) : Q (x + y) = Q x + Q y + polar Q x y :=
  QuadraticMap.map_add Q x y

theorem polar_eq (x y : V) : polar Q x y = Q (x + y) + Q x + Q y := by
  have h := map_add_polar Q x y
  generalize Q (x + y) = a at h ⊢
  generalize Q x = b at h ⊢
  generalize Q y = c at h ⊢
  generalize polar Q x y = d at h ⊢
  subst h
  revert b c d
  decide

structure MinusPair (a b : V) : Prop where
  qa : Q a = 1
  qb : Q b = 1
  ab : polar Q a b = 1

variable {Q}

theorem MinusPair.ba {a b : V} (h : MinusPair Q a b) : polar Q b a = 1 := by
  rw [polar_comm]
  exact h.ab

theorem MinusPair.symm {a b : V} (h : MinusPair Q a b) : MinusPair Q b a :=
  ⟨h.qb, h.qa, h.ba⟩

theorem MinusPair.aa {a b : V} (_ : MinusPair Q a b) : polar Q a a = 0 := polar_self_zero Q a

theorem MinusPair.bb {a b : V} (_ : MinusPair Q a b) : polar Q b b = 0 := polar_self_zero Q b

theorem MinusPair.ne_zero_left {a b : V} (h : MinusPair Q a b) : a ≠ 0 := by
  rintro rfl
  have := h.qa
  rw [QuadraticMap.map_zero] at this
  exact zero_ne_one this

end Basic

section Rot

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

variable (Q) in
@[expose] noncomputable def rot (a b : V) : V ≃ₗ[ZMod 2] V := reflect Q a * reflect Q b

theorem rot_apply {a b : V} (h : MinusPair Q a b) (x : V) :
    rot Q a b x = x + (polar Q x a + polar Q x b) • a + polar Q x b • b := by
  rw [rot, LinearEquiv.mul_apply, reflect_apply_of_map_eq_one h.qb x,
    reflect_apply_of_map_eq_one h.qa]
  simp only [polar_add_left, QuadraticMap.polar_smul_left, smul_eq_mul, h.ba, mul_one]
  module

theorem rot_apply_left {a b : V} (h : MinusPair Q a b) : rot Q a b a = b := by
  rw [rot_apply h, h.aa, h.ab]
  have := vec_add_self a
  linear_combination (norm := module) this

theorem rot_apply_right {a b : V} (h : MinusPair Q a b) : rot Q a b b = a + b := by
  rw [rot_apply h, h.bb, h.ba]
  module

theorem rot_mem_orthogonalGroup (a b : V) : rot Q a b ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  mul_mem (reflect_mem_orthogonalGroup Q a) (reflect_mem_orthogonalGroup Q b)

theorem rot_apply_of_perp {a b x : V} (h : MinusPair Q a b) (hxa : polar Q x a = 0)
    (hxb : polar Q x b = 0) : rot Q a b x = x := by
  rw [rot_apply h, hxa, hxb]
  simp

theorem pow_three_eq_one_of_braid {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b * a = b * a * b) : (a * b) ^ 3 = 1 := by
  calc (a * b) ^ 3 = (a * b * a) * (b * a * b) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = (b * a * b) * (b * a * b) := by rw [hab]
    _ = b * a * (b * b) * a * b := by simp only [mul_assoc]
    _ = 1 := by rw [hb, mul_one, mul_assoc b a a, ha, mul_one, hb]

theorem rot_pow_three {a b : V} (h : MinusPair Q a b) : rot Q a b ^ 3 = 1 := by
  have h1 := reflect_conj (reflect_mem_orthogonalGroup Q a) b
  have h2 := reflect_conj (reflect_mem_orthogonalGroup Q b) a
  rw [reflect_inv, reflect_apply_of_map_eq_one h.qa, h.ba, one_smul] at h1
  rw [reflect_inv, reflect_apply_of_map_eq_one h.qb, h.ab, one_smul, add_comm] at h2
  exact pow_three_eq_one_of_braid (reflect_mul_self Q a) (reflect_mul_self Q b) (by rw [h1, h2])

theorem rot_mem_commutator {a b : V} (h : MinusPair Q a b) :
    rot Q a b ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have hc : ⁅reflect Q a, reflect Q b⁆ ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
    Subgroup.commutator_mem_commutator (reflect_mem_orthogonalGroup Q a)
      (reflect_mem_orthogonalGroup Q b)
  have hsq : ⁅reflect Q a, reflect Q b⁆ = rot Q a b * rot Q a b := by
    rw [commutatorElement_def, reflect_inv, reflect_inv, rot]
    simp only [mul_assoc]
  have h3 := rot_pow_three h
  have h4 : rot Q a b = (rot Q a b * rot Q a b) * (rot Q a b * rot Q a b) := by
    calc rot Q a b = rot Q a b ^ 3 * rot Q a b := by rw [h3, one_mul]
      _ = _ := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [h4, ← hsq]
  exact mul_mem hc hc

theorem conj_rot {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (a b : V) :
    g * rot Q a b * g⁻¹ = rot Q (g a) (g b) := by
  rw [rot, rot, show g * (reflect Q a * reflect Q b) * g⁻¹ =
    (g * reflect Q a * g⁻¹) * (g * reflect Q b * g⁻¹) by group,
    reflect_conj hg, reflect_conj hg]

theorem reflect_commute_of_polar_eq_zero {a c : V} (h : polar Q a c = 0) :
    Commute (reflect Q a) (reflect Q c) := by
  have h1 := reflect_conj (reflect_mem_orthogonalGroup Q a) c
  rw [reflect_inv, reflect_apply_of_polar_eq_zero h] at h1
  have h2 := reflect_mul_self Q a
  calc reflect Q a * reflect Q c = reflect Q a * reflect Q c * (reflect Q a * reflect Q a) := by
        rw [h2, mul_one]
    _ = (reflect Q a * reflect Q c * reflect Q a) * reflect Q a := by simp only [mul_assoc]
    _ = reflect Q c * reflect Q a := by rw [h1]

theorem rot_commute_of_perp {a b c d : V} (hac : polar Q a c = 0) (had : polar Q a d = 0)
    (hbc : polar Q b c = 0) (hbd : polar Q b d = 0) : Commute (rot Q a b) (rot Q c d) := by
  unfold rot
  exact Commute.mul_left (Commute.mul_right (reflect_commute_of_polar_eq_zero hac)
    (reflect_commute_of_polar_eq_zero had))
    (Commute.mul_right (reflect_commute_of_polar_eq_zero hbc) (reflect_commute_of_polar_eq_zero hbd))

theorem commute_rot_of_fix {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {a b : V} (ha : g a = a) (hb : g b = b) : Commute g (rot Q a b) := by
  have h := conj_rot hg a b
  rw [ha, hb] at h
  exact mul_inv_eq_iff_eq_mul.1 h

theorem rot_sub_mem_span {a b : V} (h : MinusPair Q a b) (x : V) :
    rot Q a b x - x ∈ Submodule.span (ZMod 2) {a, b} := by
  have ha : a ∈ Submodule.span (ZMod 2) {a, b} := Submodule.subset_span (Set.mem_insert _ _)
  have hb : b ∈ Submodule.span (ZMod 2) {a, b} :=
    Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  rw [rot_apply h, add_assoc, add_sub_cancel_left]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ hb)

theorem exists_rot_sub_eq {a b : V} (h : MinusPair Q a b) {y : V}
    (hy : y ∈ Submodule.span (ZMod 2) {a, b}) : ∃ x : V, rot Q a b x - x = y := by
  have ha : rot Q a b b - b = a := by rw [rot_apply_right h]; abel
  have hb : rot Q a b (a + b) - (a + b) = b := by
    rw [map_add, rot_apply_left h, rot_apply_right h]
    abel
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.1 hy
  refine ⟨c • b + d • (a + b), ?_⟩
  rw [map_add, map_smul, map_smul]
  linear_combination (norm := module) c • ha + d • hb

end Rot

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

end
