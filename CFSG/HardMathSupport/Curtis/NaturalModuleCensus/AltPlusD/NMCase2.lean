module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltPlusD.NMPoly
public import CFSG.LieType.BorelTits.OrthogonalEichler

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open Polynomial CFSG.LieType.BorelTits

section Basic

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  (Φ : QuadForm K V) (T : V →ₗ[K] V)

theorem NM_T_inj (hT5 : T ^ 5 = 1) {x : V} (h : T x = 0) : x = 0 := by
  have : (T ^ 5) x = T (T (T (T (T x)))) := by simp [pow_succ]
  rw [hT5] at this
  simpa [h] using this

theorem NM_B_pow (hTQ : ∀ v, Φ.Q (T v) = Φ.Q v) (k : ℕ) (x y : V) :
    Φ.polar.β ((T ^ k) x) ((T ^ k) y) = Φ.polar.β x y := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, Φ.polar_map_of_Q hTQ, ih]

theorem NM_B_right_pow (hT5 : T ^ 5 = 1) (hTQ : ∀ v, Φ.Q (T v) = Φ.Q v) {k : ℕ} (hk : k ≤ 5)
    (x y : V) : Φ.polar.β x ((T ^ k) y) = Φ.polar.β ((T ^ (5 - k)) x) y := by
  have h := NM_B_pow Φ T hTQ k ((T ^ (5 - k)) x) y
  rw [← Module.End.mul_apply, ← pow_add, Nat.add_sub_cancel' hk, hT5, Module.End.one_apply] at h
  exact h

end Basic

section Case2

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  (Φ : QuadForm K V) (T : V →ₗ[K] V)

theorem NM_exists_u' (hT5 : T ^ 5 = 1) (hTQ : ∀ v, Φ.Q (T v) = Φ.Q v) {a : K}
    (ha : a ^ 2 + a + 1 = 0) {f : V} (hf0 : f ≠ 0) (hf : T (T f) = a • T f + f) :
    ∃ u' : V, T (T u') = a • T u' + u' ∧ Φ.polar.β f u' = 1 := by
  have h2 : (2 : K[X]) = 0 := NM_two_eq_zero_poly
  have ha' : (C a) ^ 2 + C a + 1 = (0 : K[X]) := by
    rw [← C_pow, ← C_1, ← C_add, ← C_add, ha, C_0]
  set hP : K[X] := X ^ 2 + C a * X + 1 with hhP
  set gP : K[X] := X ^ 3 + C a * X ^ 2 + C a * X + 1 with hgP
  have Ja : hP * gP = 0 + 1 * (X ^ 5 + 1) := by
    rw [hhP, hgP]
    linear_combination (X ^ 2 + X ^ 3 : K[X]) * ha' + (X * C a + X ^ 4 * C a) * h2
  have Jb : C a * X * gP = 1 + (C a * X ^ 2 + 1) * hP + 0 * (X ^ 5 + 1) := by
    rw [hhP, hgP]
    linear_combination (X ^ 2 : K[X]) * ha' - (X ^ 2 * C a + X ^ 2 + 1) * h2
  have Jc : X * X * gP = (1 + C a * X ^ 4 + C a * X ^ 3 + X ^ 2) + 1 * (X ^ 5 + 1) := by
    rw [hgP]
    linear_combination (-1 : K[X]) * h2
  have hfh : aeval T hP f = 0 := by
    have : T (T f) + a • T f + f = 0 := by
      linear_combination (norm := module) hf + NM_two_smul_zero (K := K) (a • T f + f)
    simpa [hhP, pow_two] using this
  set s : V := aeval T gP f with hs
  have hs1 : a • T s = f := by
    have e : aeval T (1 + (C a * X ^ 2 + 1) * hP) f = f := by
      rw [map_add, LinearMap.add_apply, NM_ev_mul, hfh]; simp
    have := NM_ev_congr T hT5 Jb f
    rw [e, NM_ev_mul T (C a * X) gP f] at this
    simpa using this
  have hs0 : s ≠ 0 := fun h => hf0 (by rw [← hs1, h]; simp)
  set w0 : V := T (T s) with hw0
  have hw0ne : w0 ≠ 0 := fun h => hs0 (NM_T_inj T hT5 (NM_T_inj T hT5 h))
  obtain ⟨v', hv'⟩ : ∃ v', Φ.polar.β w0 v' ≠ 0 := by
    by_contra! h
    exact hw0ne (Φ.polar.nondeg _ h)
  set v : V := (Φ.polar.β w0 v')⁻¹ • v' with hv
  have hBv : Φ.polar.β w0 v = 1 := by
    rw [hv, Φ.polar.smul_right, inv_mul_cancel₀ hv']
  refine ⟨aeval T gP v, ?_, ?_⟩
  · apply NM_quad_of_ev
    rw [← NM_ev_mul, NM_ev_congr T hT5 Ja]
    simp
  · have hw0' : w0 = f + a • T (T (T (T f))) + a • T (T (T f)) + T (T f) := by
      have := NM_ev_congr T hT5 Jc f
      simp only [NM_ev_mul] at this
      simp [pow_succ] at this
      exact this
    have e1 : Φ.polar.β f (T v) = Φ.polar.β (T (T (T (T f)))) v := by
      have := NM_B_right_pow Φ T hT5 hTQ (k := 1) (by norm_num) f v
      simpa [pow_succ] using this
    have e2 : Φ.polar.β f (T (T v)) = Φ.polar.β (T (T (T f))) v := by
      have := NM_B_right_pow Φ T hT5 hTQ (k := 2) (by norm_num) f v
      simpa [pow_succ] using this
    have e3 : Φ.polar.β f (T (T (T v))) = Φ.polar.β (T (T f)) v := by
      have := NM_B_right_pow Φ T hT5 hTQ (k := 3) (by norm_num) f v
      simpa [pow_succ] using this
    have hexp : aeval T gP v = T (T (T v)) + a • T (T v) + a • T v + v := by
      simp [hgP, pow_succ]
    rw [hexp, ← hBv, hw0']
    simp only [Φ.polar.add_left, Φ.polar.add_right, Φ.polar_smul_left, Φ.polar.smul_right, e1, e2,
      e3]
    ring

omit [CharP K 2] in
theorem NM_B_eq_zero_of_mem {W : Submodule K V} (hWQ : ∀ w ∈ W, Φ.Q w = 0) {x y : V}
    (hx : x ∈ W) (hy : y ∈ W) : Φ.polar.β x y = 0 := by
  have h := Φ.Q_add x y
  rw [hWQ _ (add_mem hx hy), hWQ x hx, hWQ y hy] at h
  linear_combination -h

theorem NM_fix_u (hTQ : ∀ v, Φ.Q (T v) = Φ.Q v) {a : K} (ha : a ^ 2 + a + 1 = 0) {f u' : V}
    (hQf : Φ.Q f = 0) (hBff : Φ.polar.β f (T f) = 0) (hf : T (T f) = a • T f + f)
    (hu : T (T u') = a • T u' + u') (hfu : Φ.polar.β f u' = 1) :
    ∃ u : V, Φ.Q u = 0 ∧ T (T u) = a • T u + u ∧ Φ.polar.β f u = 1 ∧
      Φ.polar.β u (T u) = 0 := by
  have h2K : (2 : K) = 0 := NM_two_eq_zero
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have hBf0 : Φ.polar.β f f = 0 := by rw [Φ.polar_self, hQf, mul_zero]
  have hBsymm : Φ.polar.β u' f = 1 := by rw [Φ.polar_symm]; exact hfu
  set c : K := Φ.Q u' with hc
  have key1 : Φ.polar.β u' (T u') = a * c := by
    have hQ2 : Φ.Q (a • T u' + u') = Φ.Q u' := by rw [← hu, hTQ, hTQ]
    rw [Φ.Q_add, Φ.Q_smul, hTQ, Φ.polar_smul_left, Φ.polar_symm (T u') u'] at hQ2
    have h3 : a * (a * c + Φ.polar.β u' (T u')) = 0 := by linear_combination hQ2
    have h4 := (mul_eq_zero.mp h3).resolve_left ha0
    linear_combination h4 - (a * c) * h2K
  have key2 : Φ.polar.β f (T u') = a + Φ.polar.β u' (T f) := by
    have h1 := Φ.polar_map_of_Q (g := T) hTQ f (T u')
    have h2 := Φ.polar_map_of_Q (g := T) hTQ f u'
    rw [hu, Φ.polar.add_right, Φ.polar.smul_right, h2, hfu, Φ.polar_symm (T f) u'] at h1
    linear_combination -h1
  refine ⟨u' + c • f, ?_, ?_, ?_, ?_⟩
  · rw [Φ.Q_add, Φ.Q_smul, hQf, Φ.polar.smul_right, hBsymm]
    linear_combination c * h2K
  · simp only [map_add, map_smul]
    linear_combination (norm := module) hu + c • hf
  · rw [Φ.polar.add_right, Φ.polar.smul_right, hBf0, hfu]
    ring
  · simp only [map_add, map_smul, Φ.polar.add_left, Φ.polar.add_right, Φ.polar_smul_left,
      Φ.polar.smul_right, key1, key2, hBff]
    linear_combination (a * c + c * Φ.polar.β u' (T f)) * h2K

theorem NM_eichler_comm (hTQ : ∀ v, Φ.Q (T v) = Φ.Q v) {a : K} {u : V} (hQu : Φ.Q u = 0)
    (hu : T (T u) = a • T u + u) (v : V) :
    Φ.eichler u (T u) (T v) = T (Φ.eichler u (T u) v) := by
  have hQTu : Φ.Q (T u) = 0 := by rw [hTQ, hQu]
  have hrel : Φ.polar.β u (T v) = Φ.polar.β (T u) v - a * Φ.polar.β u v := by
    have h1 := Φ.polar_map_of_Q (g := T) hTQ (T u) v
    have h2 := Φ.polar_map_of_Q (g := T) hTQ u v
    rw [hu, Φ.polar.add_left, Φ.polar_smul_left, h2] at h1
    linear_combination h1
  have hTT : Φ.polar.β (T u) (T v) = Φ.polar.β u v := Φ.polar_map_of_Q (g := T) hTQ u v
  simp only [QuadForm.eichler_apply, map_add, map_sub, map_smul, hQTu, zero_smul, sub_zero, hu,
    hrel, hTT]
  linear_combination (norm := module) NM_two_smul_zero (K := K)
    ((Φ.polar.β (T u) v - a * Φ.polar.β u v) • T u - Φ.polar.β u v • u)

theorem NM_false_of_quadratic [Finite K] (hK : Nat.card K = 4) (hT5 : T ^ 5 = 1)
    (hTQ : ∀ v, Φ.Q (T v) = Φ.Q v) (W : Submodule K V) (hWQ : ∀ w ∈ W, Φ.Q w = 0)
    (hW : ∀ w ∈ W, T w ∈ W)
    (hE : ∀ x y, Φ.Q x = 0 → Φ.polar.β x y = 0 →
      (∀ v, Φ.eichler x y (T v) = T (Φ.eichler x y v)) → ∀ w ∈ W, Φ.eichler x y w ∈ W)
    {a : K} (ha : a ^ 2 + a + 1 = 0) {f : V} (hfW : f ∈ W) (hf0 : f ≠ 0)
    (hf : T (T f) = a • T f + f) : False := by
  have h2K : (2 : K) = 0 := NM_two_eq_zero
  obtain ⟨u', hu', hfu'⟩ := NM_exists_u' Φ T hT5 hTQ ha hf0 hf
  have hQf := hWQ f hfW
  have hBff : Φ.polar.β f (T f) = 0 := NM_B_eq_zero_of_mem Φ hWQ hfW (hW f hfW)
  obtain ⟨u, hQu, hu, hfu, hBu⟩ := NM_fix_u Φ T hTQ ha hQf hBff hf hu' hfu'
  have hQTu : Φ.Q (T u) = 0 := by rw [hTQ, hQu]
  have hEf := hE u (T u) hQu hBu (NM_eichler_comm Φ T hTQ hQu hu) f hfW
  set β : K := Φ.polar.β (T u) f with hβ
  have hBuf : Φ.polar.β u f = 1 := by rw [Φ.polar_symm]; exact hfu
  have hz : T u - β • u ∈ W := by
    have : Φ.eichler u (T u) f - f = T u - β • u := by
      rw [QuadForm.eichler_apply, hQTu, hBuf]
      module
    rw [← this]
    exact W.sub_mem hEf hfW
  have hB0 := NM_B_eq_zero_of_mem Φ hWQ hfW (hW _ hz)
  have hBfTu : Φ.polar.β f (T u) = β := Φ.polar_symm _ _
  rw [map_sub, map_smul, hu, Φ.polar.β_sub_right, Φ.polar.add_right, Φ.polar.smul_right,
    Φ.polar.smul_right, hBfTu, hfu] at hB0
  have e : β ^ 2 = a * β + 1 := by linear_combination -hB0
  have := Fintype.ofFinite K
  have h4 : β ^ 4 = β := by
    simpa [show Fintype.card K = 4 by rw [← Nat.card_eq_fintype_card, hK]] using
      FiniteField.pow_card β
  have : a = 0 := by
    linear_combination (-1 : K) * h4 + (β ^ 2 + a * β + 1 + a ^ 2) * e +
      ((a - 1) * β + 1) * ha + (a * β) * h2K
  rw [this] at ha
  simp at ha

end Case2

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
