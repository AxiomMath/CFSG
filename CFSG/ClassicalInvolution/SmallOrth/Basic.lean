module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.ClassicalGroups.Orthogonal.Small

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

private theorem ne_zero_of_mul_mul_eq_one {c s t : K} (h : c * s * t = 1) : c ≠ 0 ∧ s ≠ 0 := by
  refine ⟨?_, ?_⟩ <;> rintro rfl <;> simp at h

variable (Q) in
@[expose] def HasAnisoPerp : Prop :=
  ∀ P : HypPair Q, ∃ a ∈ P.perp, Q a ≠ 0

theorem hasAnisoPerp_of_three_le_finrank [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 3 ≤ Module.finrank K V) : HasAnisoPerp Q := by
  classical
  intro P
  by_contra! h
  have hperp : ∀ x ∈ P.perp, x = 0 := by
    intro x hx
    refine P.polarNondegOn_perp hQ x hx fun y hy => ?_
    rw [polar, h _ (P.perp.add_mem hx hy), h x hx, h y hy]
    ring
  have hspan : (⊤ : Submodule K V) ≤ Submodule.span K {P.e, P.f} := by
    intro x _
    rw [P.eq_add_proj x, hperp _ (P.proj_mem_perp x), add_zero]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have h1 := Submodule.finrank_mono hspan
  rw [finrank_top] at h1
  have h2 := finrank_span_finset_le_card (R := K) ({P.e, P.f} : Finset V)
  have h3 : ({P.e, P.f} : Finset V).card ≤ 2 := Finset.card_le_two
  simp only [Finset.coe_insert, Finset.coe_singleton] at h2
  have h4 : Module.finrank K (Submodule.span K {P.e, P.f}) ≤ 2 := le_trans h2 h3
  omega

section Pair

variable (P : HypPair Q) {a : V} {s : K}

theorem polar_e_smul_eq_zero (ha : a ∈ P.perp) (s : K) : polar Q P.e (s • a) = 0 := by
  rw [polar_smul_right_eq, (HypPair.mem_perp.mp ha).1, mul_zero]

theorem polar_f_smul_eq_zero (ha : a ∈ P.perp) (s : K) : polar Q P.f (s • a) = 0 := by
  rw [polar_smul_right_eq, (HypPair.mem_perp.mp ha).2, mul_zero]

theorem eichler_e_apply_e (a : V) (s : K) : eichler Q P.e (s • a) P.e = P.e :=
  eichler_apply_self _ _

theorem eichler_e_apply_f (ha : a ∈ P.perp) (s : K) :
    eichler Q P.e (s • a) P.f = P.f + s • a - (s ^ 2 * Q a) • P.e := by
  rw [eichler_apply P.Q_e (polar_e_smul_eq_zero P ha s), P.polar_fe,
    polar_f_smul_eq_zero P ha s, map_smul_eq_sq]
  module

theorem eichler_e_apply_a (ha : a ∈ P.perp) (s : K) :
    eichler Q P.e (s • a) a = a - (2 * s * Q a) • P.e := by
  rw [eichler_apply P.Q_e (polar_e_smul_eq_zero P ha s), polar_comm Q a P.e,
    (HypPair.mem_perp.mp ha).1, polar_smul_right_eq, polar_self_eq_two_mul]
  module

theorem eichler_f_apply_f (a : V) (s : K) : eichler Q P.f (s • a) P.f = P.f :=
  eichler_apply_self _ _

theorem eichler_f_apply_e (ha : a ∈ P.perp) (s : K) :
    eichler Q P.f (s • a) P.e = P.e + s • a - (s ^ 2 * Q a) • P.f := by
  rw [eichler_apply P.Q_f (polar_f_smul_eq_zero P ha s), P.polar_ef,
    polar_e_smul_eq_zero P ha s, map_smul_eq_sq]
  module

theorem eichler_f_apply_a (ha : a ∈ P.perp) (s : K) :
    eichler Q P.f (s • a) a = a - (2 * s * Q a) • P.f := by
  rw [eichler_apply P.Q_f (polar_f_smul_eq_zero P ha s), polar_comm Q a P.f,
    (HypPair.mem_perp.mp ha).2, polar_smul_right_eq, polar_self_eq_two_mul]
  module

end Pair

section Weyl

variable (P : HypPair Q) {a : V}

variable (Q) in
noncomputable def weyl (P : HypPair Q) (a : V) (s t : K) : V ≃ₗ[K] V :=
  eichler Q P.e (s • a) * eichler Q P.f (t • a) * eichler Q P.e (s • a)

theorem weyl_mem (a : V) (s t : K) : weyl Q P a s t ∈ elementaryGroup Q :=
  mul_mem (mul_mem (eichler_mem_elementaryGroup Q _ _) (eichler_mem_elementaryGroup Q _ _))
    (eichler_mem_elementaryGroup Q _ _)

theorem weyl_apply_e (ha : a ∈ P.perp) {s t : K} (h : Q a * s * t = 1) :
    weyl Q P a s t P.e = (-(t ^ 2 * Q a)) • P.f := by
  unfold weyl
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, eichler_e_apply_e, eichler_f_apply_e P ha,
    map_sub, map_add, map_smul, map_smul, eichler_e_apply_e, eichler_e_apply_a P ha,
    eichler_e_apply_f P ha]
  match_scalars
  · linear_combination (Q a * s * t - 1) * h
  · linear_combination (-t) * h
  · ring

theorem weyl_apply_f (ha : a ∈ P.perp) {s t : K} (h : Q a * s * t = 1) :
    weyl Q P a s t P.f = (-(s ^ 2 * Q a)) • P.e := by
  unfold weyl
  simp only [LinearEquiv.mul_apply, map_sub, map_add, map_smul, eichler_e_apply_e,
    eichler_e_apply_f P ha, eichler_e_apply_a P ha, eichler_f_apply_f, eichler_f_apply_a P ha,
    eichler_f_apply_e P ha]
  match_scalars
  · linear_combination (Q a * s * t - 1) * h
  · linear_combination (s * (Q a * s * t - 2)) * h
  · linear_combination (-(s ^ 2 * Q a) * (Q a * s * t - 3)) * h

theorem weyl_apply_a (ha : a ∈ P.perp) {s t : K} (h : Q a * s * t = 1) :
    weyl Q P a s t a = -a := by
  unfold weyl
  simp only [LinearEquiv.mul_apply, map_sub, map_add, map_smul, eichler_e_apply_e,
    eichler_e_apply_f P ha, eichler_e_apply_a P ha, eichler_f_apply_a P ha,
    eichler_f_apply_e P ha]
  match_scalars
  · linear_combination (2 * (Q a * s * t - 1)) * h
  · linear_combination (-2 * s * Q a * (Q a * s * t - 2)) * h
  · linear_combination (2 * t * Q a) * h

theorem weyl_apply_of_perp {z : V} (hz : z ∈ P.perp) (hza : polar Q z a = 0) (s t : K) :
    weyl Q P a s t z = z := by
  have hz' := HypPair.mem_perp.mp hz
  unfold weyl
  have hA : eichler Q P.e (s • a) z = z :=
    eichler_apply_of_polar_eq_zero (by rw [polar_comm, hz'.1])
      (by rw [polar_smul_right_eq, hza, mul_zero])
  have hB : eichler Q P.f (t • a) z = z :=
    eichler_apply_of_polar_eq_zero (by rw [polar_comm, hz'.2])
      (by rw [polar_smul_right_eq, hza, mul_zero])
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hA, hB, hA]

theorem weyl_inv_apply_e (ha : a ∈ P.perp) {s t : K} (h : Q a * s * t = 1) :
    (weyl Q P a s t)⁻¹ P.e = (-(s ^ 2 * Q a)⁻¹) • P.f := by
  obtain ⟨hc, hs⟩ := ne_zero_of_mul_mul_eq_one h
  apply (weyl Q P a s t).injective
  rw [LinearEquiv.apply_inv_apply', map_smul, weyl_apply_f P ha h, smul_smul]
  have : s ^ 2 * Q a ≠ 0 := mul_ne_zero (pow_ne_zero 2 hs) hc
  rw [neg_mul_neg, inv_mul_cancel₀ this, one_smul]

theorem weyl_inv_apply_a (ha : a ∈ P.perp) {s t : K} (h : Q a * s * t = 1) :
    (weyl Q P a s t)⁻¹ a = -a := by
  apply (weyl Q P a s t).injective
  rw [LinearEquiv.apply_inv_apply', map_neg, weyl_apply_a P ha h, neg_neg]

theorem weyl_inv_apply_of_perp {z : V} (hz : z ∈ P.perp) (hza : polar Q z a = 0) (s t : K) :
    (weyl Q P a s t)⁻¹ z = z := by
  apply (weyl Q P a s t).injective
  rw [LinearEquiv.apply_inv_apply', weyl_apply_of_perp P hz hza]

theorem exists_mem_elementaryGroup_apply_e_eq_smul_f (ha : a ∈ P.perp) (hc : Q a ≠ 0) :
    ∃ g ∈ elementaryGroup Q, ∃ c : K, c ≠ 0 ∧ g P.e = c • P.f := by
  have h : Q a * 1 * (Q a)⁻¹ = 1 := by rw [mul_one, mul_inv_cancel₀ hc]
  refine ⟨weyl Q P a 1 (Q a)⁻¹, weyl_mem P a _ _, -((Q a)⁻¹ ^ 2 * Q a), ?_, weyl_apply_e P ha h⟩
  exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hc)) hc)

variable (Q) in
noncomputable def torus (P : HypPair Q) (a : V) (s₁ s₂ : K) : V ≃ₗ[K] V :=
  weyl Q P a s₁ (Q a * s₁)⁻¹ * (weyl Q P a s₂ (Q a * s₂)⁻¹)⁻¹

theorem torus_mem (a : V) (s₁ s₂ : K) : torus Q P a s₁ s₂ ∈ elementaryGroup Q :=
  mul_mem (weyl_mem P a _ _) (inv_mem (weyl_mem P a _ _))

theorem torus_mem_orthogonalGroup (a : V) (s₁ s₂ : K) :
    torus Q P a s₁ s₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  elementaryGroup_le_orthogonalGroup Q (torus_mem P a s₁ s₂)

theorem mul_mul_inv_eq_one {c s : K} (hc : c ≠ 0) (hs : s ≠ 0) : c * s * (c * s)⁻¹ = 1 :=
  mul_inv_cancel₀ (mul_ne_zero hc hs)

theorem torus_apply_e (ha : a ∈ P.perp) (hc : Q a ≠ 0) {s₁ s₂ : K} (h₁ : s₁ ≠ 0) (h₂ : s₂ ≠ 0) :
    torus Q P a s₁ s₂ P.e = (s₁ ^ 2 / s₂ ^ 2) • P.e := by
  unfold torus
  rw [LinearEquiv.mul_apply, weyl_inv_apply_e P ha (mul_mul_inv_eq_one hc h₂), map_smul,
    weyl_apply_f P ha (mul_mul_inv_eq_one hc h₁), smul_smul]
  congr 1
  field_simp

theorem torus_apply_of_mem_perp (h2 : (2 : K) ≠ 0) (ha : a ∈ P.perp) (hc : Q a ≠ 0) {s₁ s₂ : K}
    (h₁ : s₁ ≠ 0) (h₂ : s₂ ≠ 0) {w : V} (hw : w ∈ P.perp) : torus Q P a s₁ s₂ w = w := by
  set α : K := polar Q w a / (2 * Q a) with hα
  set z : V := w - α • a with hz
  have hzP : z ∈ P.perp := P.perp.sub_mem hw (P.perp.smul_mem _ ha)
  have hza : polar Q z a = 0 := by
    rw [hz, polar_sub_left, polar_smul_left_eq, polar_self_eq_two_mul, hα]
    field_simp
    ring
  have hw' : w = α • a + z := by rw [hz]; abel
  unfold torus
  rw [hw', LinearEquiv.mul_apply, map_add, map_smul,
    weyl_inv_apply_a P ha (mul_mul_inv_eq_one hc h₂),
    weyl_inv_apply_of_perp P hzP hza, map_add, map_smul, map_neg,
    weyl_apply_a P ha (mul_mul_inv_eq_one hc h₁), weyl_apply_of_perp P hzP hza]
  simp

end Weyl

section Transitive

theorem singular_f_add (P : HypPair Q) {w : V} (hw : w ∈ P.perp) :
    Q (P.f + w - Q w • P.e) = 0 ∧ polar Q P.e (P.f + w - Q w • P.e) = 1 := by
  obtain ⟨h1, h2⟩ := HypPair.mem_perp.mp hw
  constructor
  · rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_add Q, QuadraticMap.map_neg,
      map_smul_eq_sq, polar_neg_right, polar_smul_right_eq, polar_add_left, P.Q_e, P.Q_f,
      polar_comm Q w P.e, h1, P.polar_fe, h2]
    ring
  · rw [polar_sub_right, polar_add_right, polar_smul_right_eq, P.polar_ef, h1, P.polar_ee]
    ring

theorem exists_mem_elementaryGroup_apply_eq_smul_of_polar_ne_zero (hA : HasAnisoPerp Q) {x y : V}
    (hx : Q x = 0) (hy : Q y = 0) (hxy : polar Q x y ≠ 0) :
    ∃ g ∈ elementaryGroup Q, ∃ c : K, c ≠ 0 ∧ g x = c • y := by
  set b := polar Q x y
  let P : HypPair Q :=
    { e := x
      f := b⁻¹ • y
      Q_e := hx
      Q_f := by rw [map_smul_eq_sq, hy, mul_zero]
      polar_ef := by rw [polar_smul_right_eq, inv_mul_cancel₀ hxy] }
  obtain ⟨a, ha, hc⟩ := hA P
  obtain ⟨g, hg, c, hc0, hgc⟩ := exists_mem_elementaryGroup_apply_e_eq_smul_f P ha hc
  refine ⟨g, hg, c * b⁻¹, mul_ne_zero hc0 (inv_ne_zero hxy), ?_⟩
  have h : g x = c • (b⁻¹ • y) := hgc
  rw [h, smul_smul]

theorem exists_singular_polar_ne_zero_both (hQ : (polarBilin Q).Nondegenerate) {x y : V}
    (hx : Q x = 0) (hx0 : x ≠ 0) (hxy : polar Q x y = 0) (hyx : ∀ c : K, y ≠ c • x) :
    ∃ z : V, Q z = 0 ∧ polar Q x z ≠ 0 ∧ polar Q z y ≠ 0 := by
  obtain ⟨P, rfl⟩ := exists_hypPair hQ hx hx0
  have hyx' : polar Q y P.e = 0 := by rw [polar_comm, hxy]
  set α := polar Q y P.f with hα
  have hy' : P.proj y = y - α • P.e := by
    rw [HypPair.proj, hyx', zero_smul, sub_zero]
  have hy'P : y - α • P.e ∈ P.perp := hy' ▸ P.proj_mem_perp y
  have hy'0 : y - α • P.e ≠ 0 := fun h => hyx α (sub_eq_zero.mp h)
  by_cases hα0 : α = 0
  · rw [hα0, zero_smul, sub_zero] at hy'0 hy'P
    obtain ⟨w, hwP, hw⟩ := (P.polarNondegOn_perp hQ).exists_polar_ne_zero hy'P hy'0
    obtain ⟨hz1, hz2⟩ := singular_f_add P hwP
    refine ⟨_, hz1, by rw [hz2]; exact one_ne_zero, ?_⟩
    rw [polar_comm, polar_sub_right, polar_add_right, polar_smul_right_eq, hyx', ← hα, hα0]
    simpa using hw
  · refine ⟨P.f, P.Q_f, by rw [P.polar_ef]; exact one_ne_zero, ?_⟩
    rw [polar_comm]
    exact hα0

theorem exists_mem_elementaryGroup_apply_eq_smul (hQ : (polarBilin Q).Nondegenerate)
    (hA : HasAnisoPerp Q) {x y : V} (hx : Q x = 0) (hy : Q y = 0) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    ∃ g ∈ elementaryGroup Q, ∃ c : K, c ≠ 0 ∧ g x = c • y := by
  by_cases hxy : polar Q x y = 0
  swap
  · exact exists_mem_elementaryGroup_apply_eq_smul_of_polar_ne_zero hA hx hy hxy
  by_cases hyx : ∀ c : K, y ≠ c • x
  swap
  · push Not at hyx
    obtain ⟨c, rfl⟩ := hyx
    have hc : c ≠ 0 := by
      rintro rfl
      exact hy0 (zero_smul K x)
    refine ⟨1, one_mem _, c⁻¹, inv_ne_zero hc, ?_⟩
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rfl
  obtain ⟨z, hz, hez, hzy⟩ := exists_singular_polar_ne_zero_both hQ hx hx0 hxy hyx
  obtain ⟨g₁, hg₁, c₁, hc₁, h₁⟩ :=
    exists_mem_elementaryGroup_apply_eq_smul_of_polar_ne_zero hA hx hz hez
  obtain ⟨g₂, hg₂, c₂, hc₂, h₂⟩ :=
    exists_mem_elementaryGroup_apply_eq_smul_of_polar_ne_zero hA hz hy hzy
  refine ⟨g₂ * g₁, mul_mem hg₂ hg₁, c₁ * c₂, mul_ne_zero hc₁ hc₂, ?_⟩
  rw [LinearEquiv.mul_apply, h₁, map_smul, h₂, smul_smul]

end Transitive

end CFSG.ClassicalGroups.Orthogonal.Small
