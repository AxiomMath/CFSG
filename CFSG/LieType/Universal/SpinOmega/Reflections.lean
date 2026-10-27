module

public import CFSG.ClassicalGroups.Orthogonal.Derived

public section

namespace CFSG.LieType.Universal.Spin

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem reflect_smul_of_ne_zero {t : K} (ht : t ≠ 0) (v : V) :
    reflect Q (t • v) = reflect Q v := by
  by_cases hv : Q v = 0
  · rw [reflect_of_map_eq_zero hv, reflect_of_map_eq_zero (by rw [map_smul_eq_sq, hv, mul_zero])]
  · have htv : Q (t • v) ≠ 0 := by
      rw [map_smul_eq_sq]
      exact mul_ne_zero (pow_ne_zero 2 ht) hv
    refine LinearEquiv.ext fun x => ?_
    rw [reflect_apply htv, reflect_apply hv, map_smul_eq_sq, polar_smul_left_eq, smul_smul]
    congr 2
    field_simp

section Elementary

variable (hQ : (polarBilin Q).Nondegenerate) {P P' : HypPair Q} (h : P.Orth P')

include hQ h in
theorem reflect_mul_reflect_mem_of_eq_sq_mul {a b : V} (hb : Q b ≠ 0) {t : K} (ht : t ≠ 0)
    (hab : Q a = t ^ 2 * Q b) : reflect Q a * reflect Q b ∈ elementaryGroup Q := by
  have hQa : Q a = Q (t • b) := by rw [hab, map_smul_eq_sq]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hab
    exact mul_ne_zero (pow_ne_zero 2 ht) hb hab.symm
  have htb0 : t • b ≠ 0 :=
    smul_ne_zero ht fun h0 => hb (by rw [h0, QuadraticMap.map_zero])
  obtain ⟨g, hg, hga⟩ := exists_mem_elementaryGroup_apply_eq hQ h ha0 htb0 hQa
  have hgO := elementaryGroup_le_orthogonalGroup Q hg
  have hconj : reflect Q b = g * reflect Q a * g⁻¹ := by
    rw [reflect_conj hgO, hga, reflect_smul_of_ne_zero ht]
  rw [hconj, ← mul_assoc, ← mul_assoc]
  refine mul_mem ?_ (inv_mem hg)
  have := conj_mem_elementaryGroup (reflect_mem_orthogonalGroup Q a) hg
  rwa [reflect_inv] at this

private theorem map_hyp (P : HypPair Q) (c : K) : Q (P.e + c • P.f) = c := by
  rw [QuadraticMap.map_add Q, map_smul_eq_sq, polar_smul_right_eq, P.Q_e, P.Q_f, P.polar_ef]
  ring

private theorem map_hyp_ne_zero (P : HypPair Q) {c : K} (hc : c ≠ 0) :
    Q (P.e + c • P.f) ≠ 0 := by
  rwa [map_hyp]

private theorem polar_hyp (P : HypPair Q) (c : K) (x : V) :
    polar Q (P.e + c • P.f) x = polar Q P.e x + c * polar Q P.f x := by
  rw [polar_add_left, polar_smul_left_eq]

private theorem reflect_hyp_mul_reflect_hyp_apply (P : HypPair Q) {c d : K} (hc : c ≠ 0)
    (hd : d ≠ 0) (x : V) :
    (reflect Q (P.e + c • P.f) * reflect Q (P.e + d • P.f)) x =
      x + ((d / c - 1) * polar Q P.f x) • P.e + ((c / d - 1) * polar Q P.e x) • P.f := by
  rw [LinearEquiv.mul_apply, reflect_apply (map_hyp_ne_zero P hd), map_hyp, polar_hyp,
    reflect_apply (map_hyp_ne_zero P hc), map_hyp, polar_hyp]
  simp only [polar_sub_right, polar_smul_right_eq, polar_add_right, P.polar_ee, P.polar_ef,
    P.polar_fe, P.polar_ff]
  match_scalars <;> field_simp <;> ring

private theorem reflect_hyp_mul_reflect_hyp (P : HypPair Q) {c d : K} (hc : c ≠ 0)
    (hd : d ≠ 0) :
    reflect Q (P.e + c • P.f) * reflect Q (P.e + d • P.f) =
      reflect Q (P.e + (1 : K) • P.f) * reflect Q (P.e + (d / c) • P.f) := by
  refine LinearEquiv.ext fun x => ?_
  rw [reflect_hyp_mul_reflect_hyp_apply P hc hd,
    reflect_hyp_mul_reflect_hyp_apply P one_ne_zero (div_ne_zero hd hc), div_one, one_div_div]

private theorem reflect_hyp_mul_reflect_hyp_mul (P : HypPair Q) {c d : K} (hc : c ≠ 0)
    (hd : d ≠ 0) :
    reflect Q (P.e + (1 : K) • P.f) * reflect Q (P.e + c • P.f) *
        (reflect Q (P.e + (1 : K) • P.f) * reflect Q (P.e + d • P.f)) =
      reflect Q (P.e + (1 : K) • P.f) * reflect Q (P.e + (c * d) • P.f) := by
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, reflect_hyp_mul_reflect_hyp_apply P one_ne_zero hd,
    reflect_hyp_mul_reflect_hyp_apply P one_ne_zero hc,
    reflect_hyp_mul_reflect_hyp_apply P one_ne_zero (mul_ne_zero hc hd)]
  simp only [polar_add_right, polar_smul_right_eq, P.polar_ee, P.polar_ef, P.polar_fe, P.polar_ff]
  match_scalars <;> field_simp <;> ring

private theorem mul_mul_inv_mem {x₁ x₂ y₁ y₂ : V ≃ₗ[K] V}
    (hx₁ : x₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h₁ : x₁ * y₁⁻¹ ∈ elementaryGroup Q)
    (h₂ : x₂ * y₂⁻¹ ∈ elementaryGroup Q) : x₁ * x₂ * (y₁ * y₂)⁻¹ ∈ elementaryGroup Q := by
  have key : x₁ * x₂ * (y₁ * y₂)⁻¹ = x₁ * (x₂ * y₂⁻¹) * x₁⁻¹ * (x₁ * y₁⁻¹) := by group
  rw [key]
  exact mul_mem (conj_mem_elementaryGroup hx₁ h₂) h₁

private theorem mul_inv_mem_trans {x y z : V ≃ₗ[K] V} (h₁ : x * y⁻¹ ∈ elementaryGroup Q)
    (h₂ : y * z⁻¹ ∈ elementaryGroup Q) : x * z⁻¹ ∈ elementaryGroup Q := by
  have key : x * z⁻¹ = x * y⁻¹ * (y * z⁻¹) := by group
  rw [key]
  exact mul_mem h₁ h₂

private theorem conj_mul_inv_mem {g u u' T : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hu : u * u'⁻¹ ∈ elementaryGroup Q) :
    g * u * T * (g * u' * T)⁻¹ ∈ elementaryGroup Q := by
  have key : g * u * T * (g * u' * T)⁻¹ = g * (u * u'⁻¹) * g⁻¹ := by group
  rw [key]
  exact conj_mem_elementaryGroup hg hu

include hQ h

private theorem reflect_mul_inv_reflect_hyp_mem {a : V} (ha : Q a ≠ 0) :
    reflect Q a * (reflect Q (P.e + Q a • P.f))⁻¹ ∈ elementaryGroup Q := by
  rw [reflect_inv]
  exact reflect_mul_reflect_mem_of_eq_sq_mul hQ h (map_hyp_ne_zero P ha) one_ne_zero
    (by rw [map_hyp, one_pow, one_mul])

private theorem prod_reflect_mul_inv_mem : ∀ l : List V, (∀ a ∈ l, Q a ≠ 0) → Even l.length →
    (l.map (reflect Q)).prod *
        (reflect Q (P.e + (1 : K) • P.f) * reflect Q (P.e + (l.map Q).prod • P.f))⁻¹ ∈
      elementaryGroup Q
  | [], _, _ => by
    simp only [List.map_nil, List.prod_nil, one_mul, reflect_mul_self, inv_one]
    exact one_mem _
  | [_], _, hev => absurd hev (by simp)
  | a :: b :: l, hl, hev => by
    have ha : Q a ≠ 0 := hl a (by simp)
    have hb : Q b ≠ 0 := hl b (by simp)
    have hl' : ∀ c ∈ l, Q c ≠ 0 := fun c hc => hl c (by simp [hc])
    have hev' : Even l.length := by
      have : Even (l.length + 2) := by simpa using hev
      rwa [Nat.even_add, iff_true_intro even_two, iff_true] at this
    have hN : (l.map Q).prod ≠ 0 :=
      List.prod_ne_zero fun h0 => by
        obtain ⟨c, hc, hc0⟩ := List.mem_map.mp h0
        exact hl' c hc hc0
    have ih := prod_reflect_mul_inv_mem l hl' hev'
    simp only [List.map_cons, List.prod_cons]
    set N := (l.map Q).prod
    set R := (l.map (reflect Q)).prod
    have hO : ∀ v, reflect Q v ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      reflect_mem_orthogonalGroup Q
    have h1 := mul_mul_inv_mem (hO a) (reflect_mul_inv_reflect_hyp_mem hQ h ha)
      (mul_mul_inv_mem (hO b) (reflect_mul_inv_reflect_hyp_mem hQ h hb) ih)
    rw [← mul_assoc (reflect Q (P.e + Q a • P.f)), reflect_hyp_mul_reflect_hyp P ha hb] at h1
    have h2 := conj_mul_inv_mem (T := reflect Q (P.e + (1 : K) • P.f) * reflect Q (P.e + N • P.f))
      (hO (P.e + (1 : K) • P.f))
      (u := reflect Q (P.e + (Q b / Q a) • P.f)) (u' := reflect Q (P.e + (Q a * Q b) • P.f))
      (by
        rw [reflect_inv]
        refine reflect_mul_reflect_mem_of_eq_sq_mul hQ h
          (map_hyp_ne_zero P (mul_ne_zero ha hb)) (inv_ne_zero ha) ?_
        rw [map_hyp, map_hyp]
        field_simp)
    rw [reflect_hyp_mul_reflect_hyp_mul P (mul_ne_zero ha hb) hN, mul_assoc (Q a)] at h2
    exact mul_inv_mem_trans h1 h2

theorem prod_map_reflect_mem_elementaryGroup {l : List V} (hl : ∀ a ∈ l, Q a ≠ 0)
    (hev : Even l.length) (hsq : IsSquare (l.map Q).prod) :
    (l.map (reflect Q)).prod ∈ elementaryGroup Q := by
  have key := prod_reflect_mul_inv_mem hQ h l hl hev
  have hN : (l.map Q).prod ≠ 0 :=
    List.prod_ne_zero fun h0 => by
      obtain ⟨c, hc, hc0⟩ := List.mem_map.mp h0
      exact hl c hc hc0
  obtain ⟨t, ht⟩ := hsq
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [mul_zero] at ht
    exact hN ht
  have hpair : reflect Q (P.e + (1 : K) • P.f) * reflect Q (P.e + (l.map Q).prod • P.f) ∈
      elementaryGroup Q :=
    reflect_mul_reflect_mem_of_eq_sq_mul hQ h (map_hyp_ne_zero P hN) (inv_ne_zero ht0)
      (by rw [map_hyp, map_hyp, ht]; field_simp)
  have := mul_mem key hpair
  rwa [inv_mul_cancel_right] at this

end Elementary

end CFSG.LieType.Universal.Spin
