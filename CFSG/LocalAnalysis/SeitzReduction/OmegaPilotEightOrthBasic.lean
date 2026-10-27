module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotF6Factor

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal

section Matrix

variable {K : Type*} [Field K]

theorem add_eq_zero_of_fixed [CharP K 2] {a b c d x y : K} (hdet : a * d - b * c = 1)
    (h1 : a * x + b * y = x) (h2 : c * x + d * y = y) (hxy : x ≠ 0 ∨ y ≠ 0) : a + d = 0 := by
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have kx : ((a - 1) * (d - 1) - b * c) * x = 0 := by linear_combination (d - 1) * h1 - b * h2
  have ky : ((a - 1) * (d - 1) - b * c) * y = 0 := by linear_combination (a - 1) * h2 - c * h1
  have hδ : (a - 1) * (d - 1) - b * c = 0 := by
    rcases hxy with hx | hy
    · exact (mul_eq_zero.mp kx).resolve_right hx
    · exact (mul_eq_zero.mp ky).resolve_right hy
  linear_combination hdet - hδ + h2K

theorem commute_conds_of_nonscalar {a b c d α β γ δ α' β' γ' δ' : K}
    (hA : b ≠ 0 ∨ c ≠ 0 ∨ a - d ≠ 0)
    (e1 : c * β = b * γ) (e2 : γ * (a - d) = c * (α - δ)) (e3 : b * (α - δ) = β * (a - d))
    (e1' : c * β' = b * γ') (e2' : γ' * (a - d) = c * (α' - δ'))
    (e3' : b * (α' - δ') = β' * (a - d)) :
    β * γ' = β' * γ ∧ γ * (α' - δ') = γ' * (α - δ) ∧ β * (α' - δ') = β' * (α - δ) := by
  rcases hA with hb | hc | had
  · have i : β * γ' = β' * γ := by
      apply mul_left_cancel₀ hb
      linear_combination -β * e1' + β' * e1
    have iii : β * (α' - δ') = β' * (α - δ) := by
      apply mul_left_cancel₀ hb
      linear_combination β * e3' - β' * e3
    refine ⟨i, ?_, iii⟩
    apply mul_left_cancel₀ hb
    linear_combination -(α' - δ') * e1 + (α - δ) * e1' + c * iii
  · have i : β * γ' = β' * γ := by
      apply mul_left_cancel₀ hc
      linear_combination γ' * e1 - γ * e1'
    have ii : γ * (α' - δ') = γ' * (α - δ) := by
      apply mul_left_cancel₀ hc
      linear_combination -γ * e2' + γ' * e2
    refine ⟨i, ii, ?_⟩
    apply mul_left_cancel₀ hc
    linear_combination (α' - δ') * e1 - (α - δ) * e1' + b * ii
  · have ii : γ * (α' - δ') = γ' * (α - δ) := by
      apply mul_left_cancel₀ had
      linear_combination (α' - δ') * e2 - (α - δ) * e2'
    have iii : β * (α' - δ') = β' * (α - δ) := by
      apply mul_left_cancel₀ had
      linear_combination -(α' - δ') * e3 + (α - δ) * e3'
    refine ⟨?_, ii, iii⟩
    apply mul_left_cancel₀ (mul_ne_zero had had)
    linear_combination b * (α - δ) * e2' - γ' * (a - d) * e3 - b * (α' - δ') * e2 +
      γ * (a - d) * e3'

end Matrix

section Decomp

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {P₁ P₂ : HypPair Q}

variable (P₁ P₂) in
@[expose] def InW (x : V) : Prop :=
  polar Q P₁.e x = 0 ∧ polar Q P₁.f x = 0 ∧ polar Q P₂.e x = 0 ∧ polar Q P₂.f x = 0

variable (P₁ P₂) in
@[expose] def uPart (x : V) : V :=
  polar Q x P₁.f • P₁.e + polar Q x P₁.e • P₁.f + polar Q x P₂.f • P₂.e + polar Q x P₂.e • P₂.f

theorem inW_sub_uPart (h₁₂ : P₁.Orth P₂) (x : V) : InW P₁ P₂ (x - uPart P₁ P₂ x) := by
  have h21 := h₁₂.symm
  simp only [InW, uPart, polar_sub_right, polar_add_right, polar_smul_right_eq, P₁.polar_ee,
    P₁.polar_ef, P₁.polar_fe, P₁.polar_ff, P₂.polar_ee, P₂.polar_ef, P₂.polar_fe, P₂.polar_ff,
    h₁₂.ee, h₁₂.ef, h₁₂.fe, h₁₂.ff, h21.ee, h21.ef, h21.fe, h21.ff]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    first
    | (rw [polar_comm Q P₁.e x]; ring)
    | (rw [polar_comm Q P₁.f x]; ring)
    | (rw [polar_comm Q P₂.e x]; ring)
    | (rw [polar_comm Q P₂.f x]; ring)

theorem eq_sub_uPart_add (x : V) : x = (x - uPart P₁ P₂ x) + uPart P₁ P₂ x := by abel

theorem commute_of_fixW_of_fix (h₁₂ : P₁.Orth P₂) {g h : V ≃ₗ[K] V}
    (hgW : ∀ x, InW P₁ P₂ x → g x = x) (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hh : h P₁.e = P₁.e ∧ h P₁.f = P₁.f ∧ h P₂.e = P₂.e ∧ h P₂.f = P₂.f)
    (hhg : h (g P₁.e) = g P₁.e ∧ h (g P₁.f) = g P₁.f ∧ h (g P₂.e) = g P₂.e ∧
      h (g P₂.f) = g P₂.f) :
    g * h = h * g := by
  obtain ⟨h1, h2, h3, h4⟩ := hh
  obtain ⟨k1, k2, k3, k4⟩ := hhg
  have hu : ∀ x, h (uPart P₁ P₂ x) = uPart P₁ P₂ x := fun x => by
    simp only [uPart, map_add, map_smul, h1, h2, h3, h4]
  have hgu : ∀ x, h (g (uPart P₁ P₂ x)) = g (uPart P₁ P₂ x) := fun x => by
    simp only [uPart, map_add, map_smul, k1, k2, k3, k4]
  have hW : ∀ w, InW P₁ P₂ w → InW P₁ P₂ (h w) := by
    rintro w ⟨w1, w2, w3, w4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← h1, polar_map_of_mem hhO, w1]
    · rw [← h2, polar_map_of_mem hhO, w2]
    · rw [← h3, polar_map_of_mem hhO, w3]
    · rw [← h4, polar_map_of_mem hhO, w4]
  refine LinearEquiv.ext fun x => ?_
  have hx := inW_sub_uPart h₁₂ x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, eq_sub_uPart_add (P₁ := P₁) (P₂ := P₂) x,
    map_add, map_add, hu, hgW _ (hW _ hx), map_add, map_add, hgW _ hx, hgu]

end Decomp

section Plane

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {P₁ P₂ : HypPair Q}

theorem polar_comb_f₁ (h₁₂ : P₁.Orth P₂) (a c : K) : polar Q (a • P₁.e + c • P₂.e) P₁.f = a := by
  rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, P₁.polar_ef, polar_comm Q P₂.e,
    h₁₂.fe]
  ring

theorem polar_comb_f₂ (h₁₂ : P₁.Orth P₂) (a c : K) : polar Q (a • P₁.e + c • P₂.e) P₂.f = c := by
  rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, P₂.polar_ef, h₁₂.ef]
  ring

theorem comb_eq_comb (h₁₂ : P₁.Orth P₂) {a c a' c' : K}
    (h : a • P₁.e + c • P₂.e = a' • P₁.e + c' • P₂.e) : a = a' ∧ c = c' := by
  refine ⟨?_, ?_⟩
  · have := congrArg (fun v => polar Q v P₁.f) h
    simpa only [polar_comb_f₁ h₁₂] using this
  · have := congrArg (fun v => polar Q v P₂.f) h
    simpa only [polar_comb_f₂ h₁₂] using this

theorem apply_e_eq_coeff (h₁₂ : P₁.Orth P₂) {g : V ≃ₗ[K] V}
    (hc : g * eichler Q P₁.e P₂.e = eichler Q P₁.e P₂.e * g) :
    g P₁.e = polar Q (g P₁.e) P₁.f • P₁.e + polar Q (g P₁.e) P₂.f • P₂.e ∧
      g P₂.e = polar Q (g P₂.e) P₁.f • P₁.e + polar Q (g P₂.e) P₂.f • P₂.e := by
  obtain ⟨h1, h2⟩ := apply_e_of_commute h₁₂ hc
  have e1 : g P₁.e = polar Q (g P₂.f) P₂.e • P₁.e + (-polar Q (g P₂.f) P₁.e) • P₂.e := by
    rw [h1]; module
  have e2 : g P₂.e = (-polar Q (g P₁.f) P₂.e) • P₁.e + polar Q (g P₁.f) P₁.e • P₂.e := by
    rw [h2]; module
  constructor
  · conv_rhs => rw [e1, polar_comb_f₁ h₁₂, polar_comb_f₂ h₁₂]
    exact e1
  · conv_rhs => rw [e2, polar_comb_f₁ h₁₂, polar_comb_f₂ h₁₂]
    exact e2

theorem det_coeff_eq_one (h₁₂ : P₁.Orth P₂) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hc : g * eichler Q P₁.e P₂.e = eichler Q P₁.e P₂.e * g) :
    polar Q (g P₁.e) P₁.f * polar Q (g P₂.e) P₂.f -
      polar Q (g P₂.e) P₁.f * polar Q (g P₁.e) P₂.f = 1 := by
  have hd := det_eq_one_of_commute h₁₂ hg hc
  obtain ⟨h1, h2⟩ := apply_e_of_commute h₁₂ hc
  have c11 : polar Q (g P₁.e) P₁.f = polar Q (g P₂.f) P₂.e := by
    rw [h1, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, P₁.polar_ef,
      polar_comm Q P₂.e, h₁₂.fe]; ring
  have c21 : polar Q (g P₁.e) P₂.f = -polar Q (g P₂.f) P₁.e := by
    rw [h1, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, P₂.polar_ef, h₁₂.ef]; ring
  have c12 : polar Q (g P₂.e) P₁.f = -polar Q (g P₁.f) P₂.e := by
    rw [h2, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, P₁.polar_ef,
      polar_comm Q P₂.e, h₁₂.fe]; ring
  have c22 : polar Q (g P₂.e) P₂.f = polar Q (g P₁.f) P₁.e := by
    rw [h2, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, P₂.polar_ef, h₁₂.ef]; ring
  rw [c11, c21, c12, c22]
  linear_combination hd

theorem sq_fix_of_fixed [CharP K 2] (h₁₂ : P₁.Orth P₂) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hc : g * eichler Q P₁.e P₂.e = eichler Q P₁.e P₂.e * g) {x w : K}
    (hfix : g (x • P₁.e + w • P₂.e) = x • P₁.e + w • P₂.e) (hxw : x ≠ 0 ∨ w ≠ 0) :
    g (g P₁.e) = P₁.e ∧ g (g P₂.e) = P₂.e := by
  obtain ⟨h1, h2⟩ := apply_e_eq_coeff h₁₂ hc
  have hdet := det_coeff_eq_one h₁₂ hg hc
  set a := polar Q (g P₁.e) P₁.f
  set c := polar Q (g P₁.e) P₂.f
  set b := polar Q (g P₂.e) P₁.f
  set d := polar Q (g P₂.e) P₂.f
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have hv : g (x • P₁.e + w • P₂.e) = (a * x + b * w) • P₁.e + (c * x + d * w) • P₂.e := by
    rw [map_add, map_smul, map_smul, h1, h2]; module
  rw [hv] at hfix
  obtain ⟨f1, f2⟩ := comb_eq_comb h₁₂ hfix
  have htr : a + d = 0 := add_eq_zero_of_fixed hdet f1 f2 hxw
  constructor
  · have e : a * a + c * b = 1 := by linear_combination -hdet + a * htr - h2K
    rw [h1, map_add, map_smul, map_smul, h1, h2]
    calc a • (a • P₁.e + c • P₂.e) + c • (b • P₁.e + d • P₂.e)
        = (a * a + c * b) • P₁.e + (c * (a + d)) • P₂.e := by module
      _ = P₁.e := by rw [e, htr, mul_zero, zero_smul, one_smul, add_zero]
  · have e : b * c + d * d = 1 := by linear_combination -hdet + d * htr - h2K
    rw [h2, map_add, map_smul, map_smul, h1, h2]
    calc b • (a • P₁.e + c • P₂.e) + d • (b • P₁.e + d • P₂.e)
        = (b * (a + d)) • P₁.e + (b * c + d * d) • P₂.e := by module
      _ = P₂.e := by rw [e, htr, mul_zero, zero_smul, one_smul, zero_add]

theorem apply_eq_self_of_sq_of_pow {g : V ≃ₗ[K] V} {v : V} (hsq : g (g v) = v) {m : ℕ}
    (hm : Odd m) (hgm : g ^ m = 1) : g v = v := by
  obtain ⟨k, rfl⟩ := hm
  have hk : ∀ k : ℕ, (g ^ (2 * k)) v = v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, LinearEquiv.mul_apply, _root_.sq,
        LinearEquiv.mul_apply, hsq, ih]
  have h := LinearEquiv.congr_fun hgm v
  rw [pow_succ', LinearEquiv.mul_apply, hk] at h
  exact h

end Plane

section NoFixed

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {P₁ P₂ : HypPair Q}

theorem polar_comb4 (h₁₂ : P₁.Orth P₂) (x w x' w' : K) :
    polar Q (x • P₁.e + w • P₂.e + (x' • P₁.f + w' • P₂.f)) P₁.f = x ∧
      polar Q (x • P₁.e + w • P₂.e + (x' • P₁.f + w' • P₂.f)) P₂.f = w ∧
      polar Q (x • P₁.e + w • P₂.e + (x' • P₁.f + w' • P₂.f)) P₁.e = x' ∧
      polar Q (x • P₁.e + w • P₂.e + (x' • P₁.f + w' • P₂.f)) P₂.e = w' := by
  have h21 := h₁₂.symm
  simp only [polar_add_left, polar_smul_left_eq, P₁.polar_ef, P₁.polar_fe, P₁.polar_ee,
    P₁.polar_ff, P₂.polar_ef, P₂.polar_fe, P₂.polar_ee, P₂.polar_ff, h₁₂.ee, h₁₂.ef, h₁₂.fe,
    h₁₂.ff, h21.ee, h21.ef, h21.fe, h21.ff]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem uPart_eq_comb4 (x : V) :
    uPart P₁ P₂ x = polar Q x P₁.f • P₁.e + polar Q x P₂.f • P₂.e +
      (polar Q x P₁.e • P₁.f + polar Q x P₂.e • P₂.f) := by
  rw [uPart]; abel

theorem eq_one_of_fixW_of_fix_e (h₁₂ : P₁.Orth P₂) {g : V ≃ₗ[K] V}
    (hgL : g ∈ rootLevi Q P₁ P₂) (hgW : ∀ x, InW P₁ P₂ x → g x = x) (h1 : g P₁.e = P₁.e)
    (h2 : g P₂.e = P₂.e) : g = 1 := by
  obtain ⟨hf1, hf2⟩ := apply_f_of_mem_rootLevi h₁₂ hgL h1 h2
  refine LinearEquiv.ext fun x => ?_
  have hu : g (uPart P₁ P₂ x) = uPart P₁ P₂ x := by
    simp only [uPart, map_add, map_smul, h1, h2, hf1, hf2]
  calc g x = g ((x - uPart P₁ P₂ x) + uPart P₁ P₂ x) := by rw [sub_add_cancel]
    _ = (x - uPart P₁ P₂ x) + uPart P₁ P₂ x := by
        rw [map_add, hgW _ (inW_sub_uPart h₁₂ x), hu]
    _ = (1 : V ≃ₗ[K] V) x := by rw [sub_add_cancel]; rfl

theorem eq_zero_of_apply_comb_eq_self [CharP K 2] (h₁₂ : P₁.Orth P₂) {g : V ≃ₗ[K] V}
    (hgL : g ∈ rootLevi Q P₁ P₂) (hgW : ∀ x, InW P₁ P₂ x → g x = x) {m : ℕ} (hm : Odd m)
    (hgm : g ^ m = 1) (hg1 : g ≠ 1) {x w : K}
    (hfix : g (x • P₁.e + w • P₂.e) = x • P₁.e + w • P₂.e) : x = 0 ∧ w = 0 := by
  by_contra hne
  have hxw : x ≠ 0 ∨ w ≠ 0 := by
    by_contra h
    push Not at h
    exact hne h
  obtain ⟨s1, s2⟩ := sq_fix_of_fixed h₁₂ hgL.1.1 (mem_centralizer_singleton_iff.mp hgL.1.2)
    hfix hxw
  exact hg1 (eq_one_of_fixW_of_fix_e h₁₂ hgL hgW (apply_eq_self_of_sq_of_pow s1 hm hgm)
    (apply_eq_self_of_sq_of_pow s2 hm hgm))

theorem mem_rootLevi_flip {g : V ≃ₗ[K] V} (hgL : g ∈ rootLevi Q P₁ P₂) :
    g ∈ rootLevi Q (flipPair P₁) (flipPair P₂) :=
  ⟨⟨hgL.1.1, hgL.2⟩, hgL.1.2⟩

theorem inW_of_inW_flip {x : V} (hx : InW (flipPair P₁) (flipPair P₂) x) : InW P₁ P₂ x :=
  ⟨hx.2.1, hx.1, hx.2.2.2, hx.2.2.1⟩

theorem eq_zero_of_apply_comb4_eq_self [CharP K 2] (h₁₂ : P₁.Orth P₂) {g : V ≃ₗ[K] V}
    (hgL : g ∈ rootLevi Q P₁ P₂) (hgW : ∀ x, InW P₁ P₂ x → g x = x) {m : ℕ} (hm : Odd m)
    (hgm : g ^ m = 1) (hg1 : g ≠ 1) {x w x' w' : K}
    (hfix : g (x • P₁.e + w • P₂.e + (x' • P₁.f + w' • P₂.f)) =
      x • P₁.e + w • P₂.e + (x' • P₁.f + w' • P₂.f)) :
    x = 0 ∧ w = 0 ∧ x' = 0 ∧ w' = 0 := by
  have hf := orth_flipPair_flipPair h₁₂
  obtain ⟨h1, h2⟩ := apply_e_eq_coeff h₁₂ (mem_centralizer_singleton_iff.mp hgL.1.2)
  obtain ⟨k1, k2⟩ := apply_e_eq_coeff hf (mem_centralizer_singleton_iff.mp hgL.2)
  simp only [flipPair_e, flipPair_f] at k1 k2
  set a := polar Q (g P₁.e) P₁.f
  set c := polar Q (g P₁.e) P₂.f
  set b := polar Q (g P₂.e) P₁.f
  set d := polar Q (g P₂.e) P₂.f
  set a' := polar Q (g P₁.f) P₁.e
  set c' := polar Q (g P₁.f) P₂.e
  set b' := polar Q (g P₂.f) P₁.e
  set d' := polar Q (g P₂.f) P₂.e
  have hv : g (x • P₁.e + w • P₂.e + (x' • P₁.f + w' • P₂.f)) =
      (a * x + b * w) • P₁.e + (c * x + d * w) • P₂.e +
        ((a' * x' + b' * w') • P₁.f + (c' * x' + d' * w') • P₂.f) := by
    rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, h1, h2, k1, k2]
    module
  rw [hv] at hfix
  obtain ⟨q1, q2, q3, q4⟩ := polar_comb4 (Q := Q) h₁₂ (a * x + b * w) (c * x + d * w)
    (a' * x' + b' * w') (c' * x' + d' * w')
  rw [hfix] at q1 q2 q3 q4
  obtain ⟨r1, r2, r3, r4⟩ := polar_comb4 (Q := Q) h₁₂ x w x' w'
  rw [r1] at q1
  rw [r2] at q2
  rw [r3] at q3
  rw [r4] at q4
  have hP : g (x • P₁.e + w • P₂.e) = x • P₁.e + w • P₂.e := by
    rw [map_add, map_smul, map_smul, h1, h2]
    calc x • (a • P₁.e + c • P₂.e) + w • (b • P₁.e + d • P₂.e)
        = (a * x + b * w) • P₁.e + (c * x + d * w) • P₂.e := by module
      _ = x • P₁.e + w • P₂.e := by rw [← q1, ← q2]
  have hP' : g (x' • (flipPair P₁).e + w' • (flipPair P₂).e) =
      x' • (flipPair P₁).e + w' • (flipPair P₂).e := by
    simp only [flipPair_e]
    rw [map_add, map_smul, map_smul, k1, k2]
    calc x' • (a' • P₁.f + c' • P₂.f) + w' • (b' • P₁.f + d' • P₂.f)
        = (a' * x' + b' * w') • P₁.f + (c' * x' + d' * w') • P₂.f := by module
      _ = x' • P₁.f + w' • P₂.f := by rw [← q3, ← q4]
  obtain ⟨hx, hw⟩ := eq_zero_of_apply_comb_eq_self h₁₂ hgL hgW hm hgm hg1 hP
  obtain ⟨hx', hw'⟩ := eq_zero_of_apply_comb_eq_self hf (mem_rootLevi_flip hgL)
    (fun y hy => hgW y (inW_of_inW_flip hy)) hm hgm hg1 hP'
  exact ⟨hx, hw, hx', hw'⟩

theorem inW_of_apply_eq_self [CharP K 2] (h₁₂ : P₁.Orth P₂) {g : V ≃ₗ[K] V}
    (hgL : g ∈ rootLevi Q P₁ P₂) (hgW : ∀ x, InW P₁ P₂ x → g x = x) {m : ℕ} (hm : Odd m)
    (hgm : g ^ m = 1) (hg1 : g ≠ 1) {v : V} (hv : g v = v) : InW P₁ P₂ v := by
  have hu : g (uPart P₁ P₂ v) = uPart P₁ P₂ v := by
    have h := hv
    rw [eq_sub_uPart_add (P₁ := P₁) (P₂ := P₂) v, map_add, hgW _ (inW_sub_uPart h₁₂ v)] at h
    exact add_left_cancel h
  rw [uPart_eq_comb4] at hu
  obtain ⟨z1, z2, z3, z4⟩ := eq_zero_of_apply_comb4_eq_self h₁₂ hgL hgW hm hgm hg1 hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [polar_comm]; exact z3
  · rw [polar_comm]; exact z1
  · rw [polar_comm]; exact z4
  · rw [polar_comm]; exact z2

end NoFixed

section Range

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {P₁ P₂ : HypPair Q}

variable (P₁ P₂) in
@[expose] noncomputable def spanU₄ : Submodule K V :=
  Submodule.span K {P₁.e, P₂.e, P₁.f, P₂.f}

instance finiteDimensional_spanU₄ : FiniteDimensional K (spanU₄ P₁ P₂) :=
  FiniteDimensional.span_of_finite K (Set.toFinite _)

theorem comb4_mem_spanU₄ (x w x' w' : K) :
    x • P₁.e + w • P₂.e + (x' • P₁.f + w' • P₂.f) ∈ spanU₄ P₁ P₂ := by
  have h1 : P₁.e ∈ spanU₄ P₁ P₂ := Submodule.subset_span (by simp)
  have h2 : P₂.e ∈ spanU₄ P₁ P₂ := Submodule.subset_span (by simp)
  have h3 : P₁.f ∈ spanU₄ P₁ P₂ := Submodule.subset_span (by simp)
  have h4 : P₂.f ∈ spanU₄ P₁ P₂ := Submodule.subset_span (by simp)
  exact add_mem (add_mem (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2))
    (add_mem (Submodule.smul_mem _ _ h3) (Submodule.smul_mem _ _ h4))

theorem uPart_mem_spanU₄ (x : V) : uPart P₁ P₂ x ∈ spanU₄ P₁ P₂ := by
  rw [uPart_eq_comb4]; exact comb4_mem_spanU₄ _ _ _ _

theorem uPart_eq_of_mem_spanU₄ (h₁₂ : P₁.Orth P₂) {v : V} (hv : v ∈ spanU₄ P₁ P₂) :
    uPart P₁ P₂ v = v := by
  have h21 := h₁₂.symm
  induction hv using Submodule.span_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      simp only [uPart, P₁.polar_ef, P₁.polar_fe, P₁.polar_ee, P₁.polar_ff, P₂.polar_ef,
        P₂.polar_fe, P₂.polar_ee, P₂.polar_ff, h₁₂.ee, h₁₂.ef, h₁₂.fe, h₁₂.ff, h21.ee, h21.ef,
        h21.fe, h21.ff, zero_smul, one_smul, add_zero, zero_add]
  | zero => simp [uPart]
  | add x y _ _ hx hy =>
    simp only [uPart, polar_add_left, add_smul] at hx hy ⊢
    calc _ = (polar Q x P₁.f • P₁.e + polar Q x P₁.e • P₁.f + polar Q x P₂.f • P₂.e +
          polar Q x P₂.e • P₂.f) + (polar Q y P₁.f • P₁.e + polar Q y P₁.e • P₁.f +
          polar Q y P₂.f • P₂.e + polar Q y P₂.e • P₂.f) := by abel
      _ = x + y := by rw [hx, hy]
  | smul c x _ hx =>
    simp only [uPart, polar_smul_left_eq, mul_smul] at hx ⊢
    rw [← smul_add, ← smul_add, ← smul_add, hx]

theorem sub_mem_spanU₄ (h₁₂ : P₁.Orth P₂) {g : V ≃ₗ[K] V} (hgL : g ∈ rootLevi Q P₁ P₂)
    (hgW : ∀ x, InW P₁ P₂ x → g x = x) (v : V) : g v - v ∈ spanU₄ P₁ P₂ := by
  have hf := orth_flipPair_flipPair h₁₂
  obtain ⟨h1, h2⟩ := apply_e_eq_coeff h₁₂ (mem_centralizer_singleton_iff.mp hgL.1.2)
  obtain ⟨k1, k2⟩ := apply_e_eq_coeff hf (mem_centralizer_singleton_iff.mp hgL.2)
  simp only [flipPair_e, flipPair_f] at k1 k2
  have hgu : g (uPart P₁ P₂ v) ∈ spanU₄ P₁ P₂ := by
    rw [uPart_eq_comb4, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, h1, h2,
      k1, k2]
    have e : ∀ (α β γ δ α' β' γ' δ' x w x' w' : K),
        x • (α • P₁.e + γ • P₂.e) + w • (β • P₁.e + δ • P₂.e) +
          (x' • (α' • P₁.f + γ' • P₂.f) + w' • (β' • P₁.f + δ' • P₂.f)) =
        (x * α + w * β) • P₁.e + (x * γ + w * δ) • P₂.e +
          ((x' * α' + w' * β') • P₁.f + (x' * γ' + w' * δ') • P₂.f) := by
      intros; module
    rw [e]
    exact comb4_mem_spanU₄ _ _ _ _
  have hdec : g v - v = g (uPart P₁ P₂ v) - uPart P₁ P₂ v := by
    conv_lhs => rw [eq_sub_uPart_add (P₁ := P₁) (P₂ := P₂) v]
    rw [map_add, hgW _ (inW_sub_uPart h₁₂ v)]
    abel
  rw [hdec]
  exact sub_mem hgu (uPart_mem_spanU₄ v)

theorem exists_mem_spanU₄_sub_eq [CharP K 2] (h₁₂ : P₁.Orth P₂) {g : V ≃ₗ[K] V}
    (hgL : g ∈ rootLevi Q P₁ P₂) (hgW : ∀ x, InW P₁ P₂ x → g x = x) {m : ℕ} (hm : Odd m)
    (hgm : g ^ m = 1) (hg1 : g ≠ 1) {v : V} (hv : v ∈ spanU₄ P₁ P₂) :
    ∃ u ∈ spanU₄ P₁ P₂, g u - u = v := by
  let T : spanU₄ P₁ P₂ →ₗ[K] spanU₄ P₁ P₂ :=
    { toFun := fun u => ⟨g u - u, sub_mem_spanU₄ h₁₂ hgL hgW u⟩
      map_add' := fun u u' => Subtype.ext (by simp only [Submodule.coe_add, map_add]; abel)
      map_smul' := fun c u => Subtype.ext (by
        simp only [Submodule.coe_smul, map_smul, RingHom.id_apply, smul_sub]) }
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hu' : g (u : V) = u := by
      have := congrArg Subtype.val hu
      simp only [T, LinearMap.coe_mk, AddHom.coe_mk, ZeroMemClass.coe_zero] at this
      exact sub_eq_zero.mp this
    have hcomb := uPart_eq_of_mem_spanU₄ h₁₂ u.2
    rw [uPart_eq_comb4] at hcomb
    rw [← hcomb] at hu'
    obtain ⟨z1, z2, z3, z4⟩ := eq_zero_of_apply_comb4_eq_self h₁₂ hgL hgW hm hgm hg1 hu'
    apply Subtype.ext
    rw [← hcomb, z1, z2, z3, z4]
    simp
  obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective.mp hT) ⟨v, hv⟩
  exact ⟨u, u.2, congrArg Subtype.val hu⟩

theorem apply_mem_spanU₄_of_commute [CharP K 2] (h₁₂ : P₁.Orth P₂) {g s : V ≃ₗ[K] V}
    (hgL : g ∈ rootLevi Q P₁ P₂) (hgW : ∀ x, InW P₁ P₂ x → g x = x) {m : ℕ} (hm : Odd m)
    (hgm : g ^ m = 1) (hg1 : g ≠ 1) (hsg : s * g = g * s) {v : V} (hv : v ∈ spanU₄ P₁ P₂) :
    s v ∈ spanU₄ P₁ P₂ := by
  obtain ⟨u, -, rfl⟩ := exists_mem_spanU₄_sub_eq h₁₂ hgL hgW hm hgm hg1 hv
  have h := LinearEquiv.congr_fun hsg u
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h
  rw [map_sub, h]
  exact sub_mem_spanU₄ h₁₂ hgL hgW (s u)

theorem inW_apply_of_commute [CharP K 2] (h₁₂ : P₁.Orth P₂) {g s : V ≃ₗ[K] V}
    (hgL : g ∈ rootLevi Q P₁ P₂) (hgW : ∀ x, InW P₁ P₂ x → g x = x) {m : ℕ} (hm : Odd m)
    (hgm : g ^ m = 1) (hg1 : g ≠ 1) (hsg : s * g = g * s) {w : V} (hw : InW P₁ P₂ w) :
    InW P₁ P₂ (s w) := by
  refine inW_of_apply_eq_self h₁₂ hgL hgW hm hgm hg1 ?_
  have h := LinearEquiv.congr_fun hsg w
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hgW w hw] at h
  exact h.symm

end Range

section CommuteP

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {P₁ P₂ : HypPair Q}

theorem commute_conds_of_commute (h₁₂ : P₁.Orth P₂) {g k : V ≃ₗ[K] V} {a b c d x y z u : K}
    (g1 : g P₁.e = a • P₁.e + c • P₂.e) (g2 : g P₂.e = b • P₁.e + d • P₂.e)
    (k1 : k P₁.e = x • P₁.e + z • P₂.e) (k2 : k P₂.e = y • P₁.e + u • P₂.e) (hkg : k * g = g * k) :
    c * y = b * z ∧ z * (a - d) = c * (x - u) ∧ b * (x - u) = y * (a - d) := by
  have e1 := LinearEquiv.congr_fun hkg P₁.e
  have e2 := LinearEquiv.congr_fun hkg P₂.e
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at e1 e2
  have L1 : k (g P₁.e) = (a * x + c * y) • P₁.e + (a * z + c * u) • P₂.e := by
    rw [g1, map_add, map_smul, map_smul, k1, k2]; module
  have R1 : g (k P₁.e) = (x * a + z * b) • P₁.e + (x * c + z * d) • P₂.e := by
    rw [k1, map_add, map_smul, map_smul, g1, g2]; module
  have L2 : k (g P₂.e) = (b * x + d * y) • P₁.e + (b * z + d * u) • P₂.e := by
    rw [g2, map_add, map_smul, map_smul, k1, k2]; module
  have R2 : g (k P₂.e) = (y * a + u * b) • P₁.e + (y * c + u * d) • P₂.e := by
    rw [k2, map_add, map_smul, map_smul, g1, g2]; module
  rw [L1, R1] at e1
  rw [L2, R2] at e2
  obtain ⟨f1, f2⟩ := comb_eq_comb h₁₂ e1
  obtain ⟨f3, -⟩ := comb_eq_comb h₁₂ e2
  exact ⟨by linear_combination f1, by linear_combination f2, by linear_combination f3⟩

theorem commute_on_e (h₁₂ : P₁.Orth P₂) {g h h' : V ≃ₗ[K] V}
    (hgc : g * eichler Q P₁.e P₂.e = eichler Q P₁.e P₂.e * g)
    (hhc : h * eichler Q P₁.e P₂.e = eichler Q P₁.e P₂.e * h)
    (hh'c : h' * eichler Q P₁.e P₂.e = eichler Q P₁.e P₂.e * h')
    (hns : polar Q (g P₂.e) P₁.f ≠ 0 ∨ polar Q (g P₁.e) P₂.f ≠ 0 ∨
      polar Q (g P₁.e) P₁.f - polar Q (g P₂.e) P₂.f ≠ 0)
    (hhg : h * g = g * h) (hh'g : h' * g = g * h') :
    h (h' P₁.e) = h' (h P₁.e) ∧ h (h' P₂.e) = h' (h P₂.e) := by
  obtain ⟨g1, g2⟩ := apply_e_eq_coeff h₁₂ hgc
  obtain ⟨k1, k2⟩ := apply_e_eq_coeff h₁₂ hhc
  obtain ⟨l1, l2⟩ := apply_e_eq_coeff h₁₂ hh'c
  set a := polar Q (g P₁.e) P₁.f
  set c := polar Q (g P₁.e) P₂.f
  set b := polar Q (g P₂.e) P₁.f
  set d := polar Q (g P₂.e) P₂.f
  set α := polar Q (h P₁.e) P₁.f
  set γ := polar Q (h P₁.e) P₂.f
  set β := polar Q (h P₂.e) P₁.f
  set δ := polar Q (h P₂.e) P₂.f
  set α' := polar Q (h' P₁.e) P₁.f
  set γ' := polar Q (h' P₁.e) P₂.f
  set β' := polar Q (h' P₂.e) P₁.f
  set δ' := polar Q (h' P₂.e) P₂.f
  obtain ⟨c1, c2, c3⟩ := commute_conds_of_commute h₁₂ g1 g2 k1 k2 hhg
  obtain ⟨c1', c2', c3'⟩ := commute_conds_of_commute h₁₂ g1 g2 l1 l2 hh'g
  obtain ⟨i, ii, iii⟩ := commute_conds_of_nonscalar hns c1 c2 c3 c1' c2' c3'
  constructor
  · calc h (h' P₁.e) = (α' * α + γ' * β) • P₁.e + (α' * γ + γ' * δ) • P₂.e := by
          rw [l1, map_add, map_smul, map_smul, k1, k2]; module
      _ = (α * α' + γ * β') • P₁.e + (α * γ' + γ * δ') • P₂.e := by
          rw [show α' * α + γ' * β = α * α' + γ * β' by linear_combination i,
            show α' * γ + γ' * δ = α * γ' + γ * δ' by linear_combination ii]
      _ = h' (h P₁.e) := by rw [k1, map_add, map_smul, map_smul, l1, l2]; module
  · calc h (h' P₂.e) = (β' * α + δ' * β) • P₁.e + (β' * γ + δ' * δ) • P₂.e := by
          rw [l2, map_add, map_smul, map_smul, k1, k2]; module
      _ = (β * α' + δ * β') • P₁.e + (β * γ' + δ * δ') • P₂.e := by
          rw [show β' * α + δ' * β = β * α' + δ * β' by linear_combination -iii,
            show β' * γ + δ' * δ = β * γ' + δ * δ' by linear_combination -i]
      _ = h' (h P₂.e) := by rw [k2, map_add, map_smul, map_smul, l1, l2]; module

theorem nonscalar_of_ne_one [CharP K 2] (h₁₂ : P₁.Orth P₂) {g : V ≃ₗ[K] V}
    (hgL : g ∈ rootLevi Q P₁ P₂) (hgW : ∀ x, InW P₁ P₂ x → g x = x) (hg1 : g ≠ 1) :
    polar Q (g P₂.e) P₁.f ≠ 0 ∨ polar Q (g P₁.e) P₂.f ≠ 0 ∨
      polar Q (g P₁.e) P₁.f - polar Q (g P₂.e) P₂.f ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hb, hc, had⟩ := hcon
  have hgc := mem_centralizer_singleton_iff.mp hgL.1.2
  have hdet := det_coeff_eq_one h₁₂ hgL.1.1 hgc
  obtain ⟨g1, g2⟩ := apply_e_eq_coeff h₁₂ hgc
  rw [hb, hc] at hdet
  rw [hc] at g1
  rw [hb] at g2
  have hd : polar Q (g P₂.e) P₂.f = polar Q (g P₁.e) P₁.f := by linear_combination -had
  rw [hd] at hdet g2
  have ha : polar Q (g P₁.e) P₁.f = 1 := eq_one_of_mul_self_eq_one (by linear_combination hdet)
  rw [ha, one_smul, zero_smul, add_zero] at g1
  rw [ha, one_smul, zero_smul, zero_add] at g2
  exact hg1 (eq_one_of_fixW_of_fix_e h₁₂ hgL hgW g1 g2)

end CommuteP

section Perfect

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {P₁ P₂ : HypPair Q}

variable (K) in
@[expose] def fixPtSub (T : Set V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ v ∈ T, g v = v}
  mul_mem' {g h} hg hh v hv := by rw [LinearEquiv.mul_apply, hh v hv, hg v hv]
  one_mem' _ _ := rfl
  inv_mem' {g} hg v hv := by
    conv_lhs => rw [← hg v hv]
    exact LinearEquiv.inv_apply_apply' g v

theorem mem_fixPtSub {T : Set V} {g : V ≃ₗ[K] V} : g ∈ fixPtSub K T ↔ ∀ v ∈ T, g v = v := Iff.rfl

theorem commutatorElement_apply_eq_of_sub_mem {N : Submodule K V} {A B : V ≃ₗ[K] V}
    (hA : ∀ p ∈ N, A p = p) (hB : ∀ p ∈ N, B p = p) {v : V} (hAv : A v - v ∈ N)
    (hBv : B v - v ∈ N) : (A * B * A⁻¹ * B⁻¹) v = v := by
  have hAi : ∀ p ∈ N, A⁻¹ p = p := fun p hp => by
    conv_lhs => rw [← hA p hp]
    exact LinearEquiv.inv_apply_apply' A p
  have hBi' : B⁻¹ v = v - (B v - v) := by
    apply B.injective
    rw [LinearEquiv.apply_inv_apply', map_sub, hB _ hBv]; abel
  have hAi' : A⁻¹ v = v - (A v - v) := by
    apply A.injective
    rw [LinearEquiv.apply_inv_apply', map_sub, hA _ hAv]; abel
  calc (A * B * A⁻¹ * B⁻¹) v = A (B (A⁻¹ (B⁻¹ v))) := by simp only [LinearEquiv.mul_apply]
    _ = A (B (A⁻¹ (v - (B v - v)))) := by rw [hBi']
    _ = A (B (v - (A v - v) - (B v - v))) := by rw [map_sub, hAi _ hBv, hAi']
    _ = A (v - (A v - v)) := by
        congr 1
        rw [show v - (A v - v) - (B v - v) = v - ((A v - v) + (B v - v)) by abel, map_sub,
          map_add, hB _ hAv, hB _ hBv]
        abel
    _ = v := by rw [map_sub, hA _ hAv]; abel

theorem fix_e_of_perfect (h₁₂ : P₁.Orth P₂) {g : V ≃ₗ[K] V}
    (hgc : g * eichler Q P₁.e P₂.e = eichler Q P₁.e P₂.e * g)
    (hns : polar Q (g P₂.e) P₁.f ≠ 0 ∨ polar Q (g P₁.e) P₂.f ≠ 0 ∨
      polar Q (g P₁.e) P₁.f - polar Q (g P₂.e) P₂.f ≠ 0)
    {R : Subgroup (V ≃ₗ[K] V)} (hRz : R ≤ centralizer {eichler Q P₁.e P₂.e})
    (hRg : R ≤ centralizer {g}) (hRperf : ⁅R, R⁆ = R) :
    R ≤ fixPtSub K {P₁.e, P₂.e} := by
  have hz : ∀ r ∈ R, r * eichler Q P₁.e P₂.e = eichler Q P₁.e P₂.e * r := fun r hr =>
    mem_centralizer_singleton_iff.mp (hRz hr)
  have hg : ∀ r ∈ R, r * g = g * r := fun r hr => mem_centralizer_singleton_iff.mp (hRg hr)
  have hcomm : ∀ r ∈ R, ∀ r' ∈ R, ∀ x w : K,
      r (r' (x • P₁.e + w • P₂.e)) = r' (r (x • P₁.e + w • P₂.e)) := by
    intro r hr r' hr' x w
    obtain ⟨c1, c2⟩ := commute_on_e h₁₂ hgc (hz r hr) (hz r' hr') hns (hg r hr) (hg r' hr')
    simp only [map_add, map_smul, c1, c2]
  rw [← hRperf, Subgroup.commutator_le]
  intro r hr r' hr'
  rw [mem_fixPtSub]
  intro v hv
  have hv' : ∃ x w : K, r'⁻¹ v = x • P₁.e + w • P₂.e := by
    have hri := hz _ (inv_mem hr')
    obtain ⟨k1, k2⟩ := apply_e_eq_coeff h₁₂ hri
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact ⟨_, _, k1⟩
    · exact ⟨_, _, k2⟩
  obtain ⟨x, w, hxw⟩ := hv'
  rw [commutatorElement_def, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    hxw, hcomm _ hr' _ (inv_mem hr), ← hxw, LinearEquiv.apply_inv_apply',
    LinearEquiv.apply_inv_apply']

theorem fix_f_of_perfect (h₁₂ : P₁.Orth P₂) {R : Subgroup (V ≃ₗ[K] V)}
    (hRO : R ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hRe : R ≤ fixPtSub K {P₁.e, P₂.e})
    (hRU : ∀ r ∈ R, r P₁.f ∈ spanU₄ P₁ P₂ ∧ r P₂.f ∈ spanU₄ P₁ P₂) (hRperf : ⁅R, R⁆ = R) :
    R ≤ fixPtSub K {P₁.f, P₂.f} := by
  set N : Submodule K V := Submodule.span K {P₁.e, P₂.e} with hN
  have hfixN : ∀ r ∈ R, ∀ p ∈ N, r p = p := by
    intro r hr p hp
    have h1 : r P₁.e = P₁.e := (mem_fixPtSub.mp (hRe hr)) _ (by simp)
    have h2 : r P₂.e = P₂.e := (mem_fixPtSub.mp (hRe hr)) _ (by simp)
    induction hp using Submodule.span_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact h1
      · exact h2
    | zero => exact map_zero r
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul c x _ hx => rw [map_smul, hx]
  have hmove : ∀ r ∈ R, r P₁.f - P₁.f ∈ N ∧ r P₂.f - P₂.f ∈ N := by
    intro r hr
    have h1 : r P₁.e = P₁.e := (mem_fixPtSub.mp (hRe hr)) _ (by simp)
    have h2 : r P₂.e = P₂.e := (mem_fixPtSub.mp (hRe hr)) _ (by simp)
    have hO := hRO hr
    have key : ∀ (f : V) (u : V), u ∈ spanU₄ P₁ P₂ → polar Q u P₁.e = polar Q f P₁.e →
        polar Q u P₂.e = polar Q f P₂.e → (f = P₁.f ∨ f = P₂.f) → u - f ∈ N := by
      intro f u hu hu1 hu2 hf
      have hc := uPart_eq_of_mem_spanU₄ h₁₂ hu
      rcases hf with rfl | rfl
      · rw [P₁.polar_fe] at hu1
        rw [h₁₂.fe] at hu2
        rw [← hc, uPart, hu1, hu2, one_smul, zero_smul, add_zero,
          show polar Q u P₁.f • P₁.e + P₁.f + polar Q u P₂.f • P₂.e - P₁.f =
            polar Q u P₁.f • P₁.e + polar Q u P₂.f • P₂.e by abel]
        exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      · rw [P₂.polar_fe] at hu2
        rw [polar_comm Q P₂.f, h₁₂.ef] at hu1
        rw [← hc, uPart, hu1, hu2, one_smul, zero_smul, add_zero,
          show polar Q u P₁.f • P₁.e + polar Q u P₂.f • P₂.e + P₂.f - P₂.f =
            polar Q u P₁.f • P₁.e + polar Q u P₂.f • P₂.e by abel]
        exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    refine ⟨key _ _ (hRU r hr).1 ?_ ?_ (Or.inl rfl), key _ _ (hRU r hr).2 ?_ ?_ (Or.inr rfl)⟩
    · conv_lhs => rw [← h1]
      exact polar_map_of_mem hO _ _
    · conv_lhs => rw [← h2]
      exact polar_map_of_mem hO _ _
    · conv_lhs => rw [← h1]
      exact polar_map_of_mem hO _ _
    · conv_lhs => rw [← h2]
      exact polar_map_of_mem hO _ _
  rw [← hRperf, Subgroup.commutator_le]
  intro r hr r' hr'
  rw [mem_fixPtSub]
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rw [commutatorElement_def]
  rcases hv with rfl | rfl
  · exact commutatorElement_apply_eq_of_sub_mem (hfixN r hr) (hfixN r' hr') (hmove r hr).1
      (hmove r' hr').1
  · exact commutatorElement_apply_eq_of_sub_mem (hfixN r hr) (hfixN r' hr') (hmove r hr).2
      (hmove r' hr').2

end Perfect

theorem le_of_normalized_of_simple {G : Type*} [Group G] {S : Subgroup G}
    (hS : ∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤) {z : G} (hzS : z ∈ S) (hz1 : z ≠ 1)
    {N : Subgroup G} (hzN : z ∈ N) (hN : ∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N) : S ≤ N := by
  have hn : (N.subgroupOf S).Normal :=
    ⟨fun n hn s => mem_subgroupOf.mpr (hN _ s.2 _ (mem_subgroupOf.mp hn))⟩
  rcases hS _ hn with h | h
  · exfalso
    have hz : (⟨z, hzS⟩ : S) ∈ N.subgroupOf S := mem_subgroupOf.mpr hzN
    rw [h, mem_bot] at hz
    exact hz1 (congrArg Subtype.val hz)
  · intro x hx
    have : (⟨x, hx⟩ : S) ∈ N.subgroupOf S := h ▸ mem_top _
    exact mem_subgroupOf.mp this

section Model

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {P₁ P₂ : HypPair Q}

theorem eichler_apply_of_inW {x : V} (hx : InW P₁ P₂ x) :
    eichler Q P₁.e P₂.e x = x :=
  eichler_apply_of_polar_eq_zero (by rw [polar_comm]; exact hx.1)
    (by rw [polar_comm]; exact hx.2.2.1)

theorem commute_of_model [CharP K 2] (h₁₂ : P₁.Orth P₂) {g : V ≃ₗ[K] V}
    (hgL : g ∈ rootLevi Q P₁ P₂) (hgW : ∀ x, InW P₁ P₂ x → g x = x) {m : ℕ} (hm : Odd m)
    (hgm : g ^ m = 1) (hg1 : g ≠ 1) {S R : Subgroup (V ≃ₗ[K] V)}
    (hSg : S ≤ centralizer {g})
    (hSgen : ∀ N : Subgroup (V ≃ₗ[K] V), eichler Q P₁.e P₂.e ∈ N →
      (∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N) → S ≤ N)
    (hRO : R ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hRz : R ≤ centralizer {eichler Q P₁.e P₂.e}) (hRg : R ≤ centralizer {g})
    (hRperf : ⁅R, R⁆ = R) {s r : V ≃ₗ[K] V} (hs : s ∈ S) (hr : r ∈ R) : s * r = r * s := by
  have hgc := mem_centralizer_singleton_iff.mp hgL.1.2
  have hsg : ∀ s ∈ S, s * g = g * s := fun s hs => mem_centralizer_singleton_iff.mp (hSg hs)
  have hSW : S ≤ fixPtSub K {x | InW P₁ P₂ x} := by
    refine hSgen _ (by rw [mem_fixPtSub]; intro x hx; exact eichler_apply_of_inW hx) ?_
    intro s' hs' n hn
    rw [mem_fixPtSub]
    intro w hw
    have hn' := mem_fixPtSub.mp hn
    have hsi : s'⁻¹ * g = g * s'⁻¹ := hsg _ (inv_mem hs')
    have hw' : InW P₁ P₂ (s'⁻¹ w) := inW_apply_of_commute h₁₂ hgL hgW hm hgm hg1 hsi hw
    simp only [LinearEquiv.mul_apply]
    rw [hn' _ hw', LinearEquiv.apply_inv_apply']
  have hns := nonscalar_of_ne_one h₁₂ hgL hgW hg1
  have hRe := fix_e_of_perfect h₁₂ hgc hns hRz hRg hRperf
  have hU4 : ∀ {k : V ≃ₗ[K] V}, k * g = g * k → ∀ v ∈ spanU₄ P₁ P₂, k v ∈ spanU₄ P₁ P₂ :=
    fun hk v hv => apply_mem_spanU₄_of_commute h₁₂ hgL hgW hm hgm hg1 hk hv
  have hmemU : P₁.e ∈ spanU₄ P₁ P₂ ∧ P₂.e ∈ spanU₄ P₁ P₂ ∧ P₁.f ∈ spanU₄ P₁ P₂ ∧
      P₂.f ∈ spanU₄ P₁ P₂ :=
    ⟨Submodule.subset_span (by simp), Submodule.subset_span (by simp),
      Submodule.subset_span (by simp), Submodule.subset_span (by simp)⟩
  have hRf := fix_f_of_perfect h₁₂ hRO hRe (fun r hr =>
    ⟨hU4 (mem_centralizer_singleton_iff.mp (hRg hr)) _ hmemU.2.2.1,
      hU4 (mem_centralizer_singleton_iff.mp (hRg hr)) _ hmemU.2.2.2⟩) hRperf
  have r1 : r P₁.e = P₁.e := (mem_fixPtSub.mp (hRe hr)) _ (by simp)
  have r2 : r P₂.e = P₂.e := (mem_fixPtSub.mp (hRe hr)) _ (by simp)
  have r3 : r P₁.f = P₁.f := (mem_fixPtSub.mp (hRf hr)) _ (by simp)
  have r4 : r P₂.f = P₂.f := (mem_fixPtSub.mp (hRf hr)) _ (by simp)
  have hrU : ∀ v ∈ spanU₄ P₁ P₂, r v = v := by
    intro v hv
    rw [← uPart_eq_of_mem_spanU₄ h₁₂ hv]
    simp only [uPart, map_add, map_smul, r1, r2, r3, r4]
  have hsS := hsg s hs
  refine commute_of_fixW_of_fix h₁₂ (fun x hx => (mem_fixPtSub.mp (hSW hs)) x hx) (hRO hr)
    ⟨r1, r3, r2, r4⟩ ⟨hrU _ (hU4 hsS _ hmemU.1), hrU _ (hU4 hsS _ hmemU.2.2.1),
      hrU _ (hU4 hsS _ hmemU.2.1), hrU _ (hU4 hsS _ hmemU.2.2.2)⟩

end Model

end CFSG.SeitzReduction.OmegaPilot
