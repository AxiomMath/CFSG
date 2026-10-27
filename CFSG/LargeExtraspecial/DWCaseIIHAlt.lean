module

public import Mathlib
public import CFSG.ClassicalGroups.Alternating.Generation
public import CFSG.GroupTheory.GLnTwoSplitting.FirstCohomology

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Module Submodule
open LinearMap (BilinForm)

macro "zmod_two_module" : tactic =>
  `(tactic| (match_scalars; all_goals (try ring_nf); all_goals (try reduce_mod_char)))

macro "abel_two" : tactic =>
  `(tactic| (abel_nf; simp only [← Int.cast_smul_eq_zsmul (ZMod 2),
    ← Nat.cast_smul_eq_nsmul (ZMod 2)]; reduce_mod_char; try simp))

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def IsAltEnd (ω : BilinForm (ZMod 2) V) (φ : Module.End (ZMod 2) V) : Prop :=
  ∀ x, ω x (φ x) = 0

@[expose] def sw (ω : BilinForm (ZMod 2) V) (a b : V) : Module.End (ZMod 2) V :=
  (ω.flip b).smulRight a + (ω.flip a).smulRight b

@[expose] def tv (ω : BilinForm (ZMod 2) V) (v : V) : Module.End (ZMod 2) V :=
  LinearMap.id + (ω.flip v).smulRight v

variable (ω : BilinForm (ZMod 2) V)

theorem sw_apply (a b x : V) : sw ω a b x = ω x b • a + ω x a • b := rfl

theorem tv_apply (v x : V) : tv ω v x = x + ω x v • v := rfl

theorem zmod_two_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b :=
  (add_eq_zero_iff_eq_neg.mp h).trans (ZModModule.neg_eq_self b)

theorem vec_eq_of_add_eq_zero {x y : V} (h : x + y = 0) : x = y :=
  (add_eq_zero_iff_eq_neg.mp h).trans (ZModModule.neg_eq_self y)

theorem sw_comm (a b : V) : sw ω a b = sw ω b a := by
  ext x
  simp only [sw_apply]
  exact add_comm _ _

theorem sw_self (a : V) : sw ω a a = 0 := by
  ext x
  rw [sw_apply, ZModModule.add_self]
  rfl

theorem sw_add_right (a b c : V) : sw ω a (b + c) = sw ω a b + sw ω a c := by
  ext x
  simp only [sw_apply, map_add, add_smul, smul_add, LinearMap.add_apply]
  abel

theorem sw_smul_right (a b : V) (c : ZMod 2) : sw ω a (c • b) = c • sw ω a b := by
  ext x
  simp only [sw_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_add, smul_smul]
  ring_nf

variable {ω}

theorem IsAltEnd.symm {φ : Module.End (ZMod 2) V} (hφ : IsAltEnd ω φ) (x y : V) :
    ω x (φ y) = ω y (φ x) := by
  have h := hφ (x + y)
  simp only [map_add, LinearMap.add_apply, hφ x, hφ y, zero_add, add_zero] at h
  exact (zmod_two_eq_of_add_eq_zero h).symm

theorem IsAltEnd.adj (hω : ω.IsAlt) {φ : Module.End (ZMod 2) V} (hφ : IsAltEnd ω φ) (x y : V) :
    ω (φ x) y = ω x (φ y) := by
  rw [← hω.neg_eq, ZModModule.neg_eq_self, hφ.symm]

theorem bilin_comm_of_isAlt (hω : ω.IsAlt) (x y : V) : ω x y = ω y x := by
  rw [← hω.neg_eq, ZModModule.neg_eq_self]

theorem mem_span_singleton_iff_zmod_two {x v : V} :
    x ∈ span (ZMod 2) {v} ↔ x = 0 ∨ x = v := by
  rw [mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    rcases CFSG.GroupTheory.GLnTwoSplitting.zmod_two_eq_zero_or_one c with rfl | rfl
    · exact Or.inl (zero_smul _ _)
    · exact Or.inr (one_smul _ _)
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

variable (ω) in
theorem tv_tv (hω : ω.IsAlt) (v x : V) : tv ω v (tv ω v x) = x := by
  rw [tv_apply, tv_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    hω.self_eq_zero, smul_zero, add_zero, add_assoc, ZModModule.add_self, add_zero]

theorem tv_isometry (hω : ω.IsAlt) (v x y : V) : ω (tv ω v x) (tv ω v y) = ω x y := by
  have h := bilin_comm_of_isAlt hω v y
  simp only [tv_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    hω.self_eq_zero, smul_eq_mul, mul_zero, add_zero, h]
  rw [add_assoc, mul_comm (ω y v), CharTwo.add_self_eq_zero, add_zero]

theorem apply_tv_apply {g h : Module.End (ZMod 2) V} (hg : ∀ x y, ω (g x) (g y) = ω x y)
    (hgh : ∀ x, g (h x) = x) (v x : V) : g (tv ω v (h x)) = tv ω (g v) x := by
  rw [tv_apply, map_add, map_smul, hgh, tv_apply, ← hg, hgh]

theorem apply_sw_apply {g h : Module.End (ZMod 2) V} (hg : ∀ x y, ω (g x) (g y) = ω x y)
    (hgh : ∀ x, g (h x) = x) (a b x : V) : g (sw ω a b (h x)) = sw ω (g a) (g b) x := by
  rw [sw_apply, map_add, map_smul, map_smul, sw_apply, ← hg (h x) b, ← hg (h x) a, hgh]

theorem tv_comp_comp_tv (hω : ω.IsAlt) {φ : Module.End (ZMod 2) V} (hφ : IsAltEnd ω φ)
    (v x : V) : tv ω v (φ (tv ω v x)) = φ x + sw ω v (φ v) x := by
  have h1 : ω (φ x) v = ω x (φ v) := hφ.adj hω x v
  have h2 : ω (φ v) v = 0 := by rw [hφ.adj hω, hφ v]
  rw [tv_apply, tv_apply, map_add, map_smul, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, h1, h2, smul_zero, add_zero, sw_apply]
  abel

theorem tv_comm (hω : ω.IsAlt) {u v : V} (huv : ω u v = 0) (x : V) :
    tv ω u (tv ω v x) = tv ω v (tv ω u x) := by
  have hvu : ω v u = 0 := by rw [bilin_comm_of_isAlt hω, huv]
  rw [tv_apply, tv_apply, tv_apply, tv_apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, hvu, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, huv, smul_zero, add_zero, smul_zero, add_zero]
  abel

theorem tv_tv_tv (hω : ω.IsAlt) {u v : V} (huv : ω u v = 1) (x : V) :
    tv ω u (tv ω v (tv ω u x)) = tv ω (u + v) x := by
  have h : tv ω u v = u + v := by
    rw [tv_apply, bilin_comm_of_isAlt hω v u, huv, one_smul, add_comm]
  rw [apply_tv_apply (tv_isometry hω u) (tv_tv ω hω u), h]

theorem tv_four (hω : ω.IsAlt) {a b c : V} (hab : ω a b = 0) (hac : ω a c = 0)
    (hbc : ω b c = 0) (x : V) :
    tv ω a (tv ω b (tv ω c (tv ω (a + b + c) x))) =
      tv ω (a + c) (tv ω (b + c) (tv ω (a + b) x)) := by
  have hba : ω b a = 0 := by rw [bilin_comm_of_isAlt hω, hab]
  have hca : ω c a = 0 := by rw [bilin_comm_of_isAlt hω, hac]
  have hcb : ω c b = 0 := by rw [bilin_comm_of_isAlt hω, hbc]
  simp [tv_apply, hab, hac, hbc, hba, hca, hcb, hω.self_eq_zero]
  module

variable [FiniteDimensional (ZMod 2) V]

theorem exists_apply_eq_one_of_notMem (hω : ω.IsAlt) (hnd : ω.Nondegenerate)
    {N : Submodule (ZMod 2) V} {p : V} (hp : p ∉ N) :
    ∃ x, (∀ n ∈ N, ω x n = 0) ∧ ω x p = 1 := by
  rw [← LinearMap.BilinForm.orthogonal_orthogonal hnd hω.isRefl N,
    LinearMap.BilinForm.mem_orthogonal_iff] at hp
  push Not at hp
  obtain ⟨x, hx, hxp⟩ := hp
  refine ⟨x, fun n hn => hω.eq_iff.mp (LinearMap.BilinForm.mem_orthogonal_iff.mp hx n hn), ?_⟩
  rcases CFSG.GroupTheory.GLnTwoSplitting.zmod_two_eq_zero_or_one (ω x p) with h | h
  · exact absurd h hxp
  · exact h

theorem mem_span_of_sw_eq_zero (hω : ω.IsAlt) (hnd : ω.Nondegenerate) {a b : V} (ha : a ≠ 0)
    (h : sw ω a b = 0) : b ∈ span (ZMod 2) {a} := by
  by_contra hb
  obtain ⟨x, hx, hxb⟩ := exists_apply_eq_one_of_notMem hω hnd hb
  have h1 := LinearMap.congr_fun h x
  rw [sw_apply, hxb, hx a (mem_span_singleton_self a), one_smul, zero_smul, add_zero,
    LinearMap.zero_apply] at h1
  exact ha h1

theorem mem_span_pair_of_sw_eq_sw (hω : ω.IsAlt) (hnd : ω.Nondegenerate) {u v p q : V}
    (hu : u ∉ span (ZMod 2) {v}) (h : sw ω u p = sw ω v q) : p ∈ span (ZMod 2) {u, v} := by
  by_contra hp
  obtain ⟨x, hx, hxp⟩ := exists_apply_eq_one_of_notMem hω hnd hp
  have h1 := LinearMap.congr_fun h x
  rw [sw_apply, sw_apply, hxp, hx u (subset_span (by simp)), hx v (subset_span (by simp)),
    one_smul, zero_smul, add_zero, zero_smul, add_zero] at h1
  exact hu (h1 ▸ smul_mem _ _ (mem_span_singleton_self v))

end CFSG.LargeExtraspecial.DW
