module

public import CFSG.FeitThompson.Representations.UnitInnerProductSignedPair

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

variable {G : Type*} [Group G]

section Aux

variable {α : Type*} [Fintype α]

theorem cfInner_sum_right {ι : Type*} (f : α → ℂ) (s : Finset ι) (F : ι → α → ℂ) :
    cfInner f (∑ i ∈ s, F i) = ∑ i ∈ s, cfInner f (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cfInner_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, cfInner_add_right, ih, Finset.sum_insert ha]

theorem cfInner_conj_conj (f h : α → ℂ) :
    cfInner (fun x => conj (f x)) (fun x => conj (h x)) = conj (cfInner f h) := by
  simp only [cfInner_def, map_mul, map_sum, map_inv₀, Complex.conj_natCast, Complex.conj_conj]

theorem cfInner_conj_left_of_conj_eq_neg (f : α → ℂ) {Ψ : α → ℂ}
    (hΨ : ∀ x, conj (Ψ x) = -Ψ x) :
    cfInner (fun x => conj (f x)) Ψ = -conj (cfInner f Ψ) := by
  have h : (fun x => conj ((-Ψ) x)) = Ψ := by
    funext x; rw [Pi.neg_apply, map_neg, hΨ, neg_neg]
  calc cfInner (fun x => conj (f x)) Ψ
      = cfInner (fun x => conj (f x)) (fun x => conj ((-Ψ) x)) := by rw [h]
    _ = conj (cfInner f (-Ψ)) := cfInner_conj_conj _ _
    _ = -conj (cfInner f Ψ) := by rw [cfInner_neg_right, map_neg]

end Aux

theorem eq_or_eq_neg_of_cfInner_ne_zero [Fintype G] {a b : G → ℂ} (ha : a ∈ signedIrr G)
    (hb : b ∈ signedIrr G) (h : cfInner a b ≠ 0) : a = b ∨ a = -b := by
  rcases cfInner_eq_zero_or_one_or_neg_one_of_mem_signedIrr ha hb with h0 | h1 | h2
  · exact absurd h0 h
  · exact Or.inl (eq_of_cfInner_eq_one ha hb h1)
  · have h3 : cfInner (-a) b = 1 := by rw [cfInner_neg_left, h2, neg_neg]
    exact Or.inr (neg_eq_iff_eq_neg.1
      (eq_of_cfInner_eq_one (neg_mem_signedIrr_iff.2 ha) hb h3))

theorem conj_cfInner_eq_self_of_mem_signedIrr [Fintype G] {a b : G → ℂ}
    (ha : a ∈ signedIrr G) (hb : b ∈ signedIrr G) : conj (cfInner a b) = cfInner a b := by
  rcases cfInner_eq_zero_or_one_or_neg_one_of_mem_signedIrr ha hb with h | h | h <;>
    rw [h] <;> simp

theorem cfInner_eq_zero_of_conj_eq_neg_of_disjoint_support [Fintype G]
    {R T : Finset (G → ℂ)} (hR : ∀ a ∈ R, a ∈ signedIrr G) (hT : ∀ b ∈ T, b ∈ signedIrr G)
    (hTortho : ∀ b ∈ T, ∀ b' ∈ T, cfInner b b' = if b = b' then 1 else 0)
    {D E : Set G} (hDE : Disjoint D E)
    (hΨconj : ∀ x, conj ((∑ b ∈ T, b) x) = -((∑ b ∈ T, b) x))
    (hΨE : ∀ x ∉ E, (∑ b ∈ T, b) x = 0)
    (hRD : ∀ a ∈ R, ∀ x ∉ D, a x - conj (a x) = 0)
    {a b : G → ℂ} (ha : a ∈ R) (hb : b ∈ T) : cfInner a b = 0 := by
  classical
  set Ψ : G → ℂ := ∑ b ∈ T, b with hΨdef
  set c : ℂ := cfInner a Ψ with hc
  have hcsum : c = ∑ b' ∈ T, cfInner a b' := by
    rw [hc, hΨdef]; exact cfInner_sum_right a T (fun b => b)
  have hcreal : conj c = c := by
    rw [hcsum, map_sum]
    exact Finset.sum_congr rfl fun b' hb' =>
      conj_cfInner_eq_self_of_mem_signedIrr (hR a ha) (hT b' hb')
  have hsupp : Disjoint (Function.support (a - fun x => conj (a x))) (Function.support Ψ) := by
    refine Set.disjoint_left.2 fun x hx hy => ?_
    have hxD : x ∈ D := by
      by_contra h
      exact hx (by simpa using hRD a ha x h)
    have hxE : x ∈ E := by
      by_contra h
      exact hy (hΨE x h)
    exact Set.disjoint_left.1 hDE hxD hxE
  have hzero : cfInner (a - fun x => conj (a x)) Ψ = 0 :=
    cfInner_eq_zero_of_disjoint_support hsupp
  rw [cfInner_sub_left, cfInner_conj_left_of_conj_eq_neg a hΨconj, ← hc, hcreal, sub_neg_eq_add]
    at hzero
  have hc0 : c = 0 := by
    have h2 : (2 : ℂ) * c = 0 := by rw [two_mul]; exact hzero
    simpa using h2
  by_contra hab
  rcases eq_or_eq_neg_of_cfInner_ne_zero (hR a ha) (hT b hb) hab with rfl | rfl
  · have h1 : c = 1 := by
      rw [hcsum, Finset.sum_congr rfl fun b' hb' => hTortho a hb b' hb']
      simp [Finset.sum_ite_eq, hb]
    rw [hc0] at h1; exact zero_ne_one h1
  · have h1 : c = -1 := by
      rw [hcsum, Finset.sum_congr rfl fun b' hb' => by
        rw [cfInner_neg_left, hTortho b hb b' hb']]
      simp [Finset.sum_ite_eq, hb]
    rw [hc0] at h1; norm_num at h1

theorem forall_cfInner_eq_zero_of_conj_eq_neg_of_disjoint_support [Fintype G]
    {R T : Finset (G → ℂ)} (hR : ∀ a ∈ R, a ∈ signedIrr G) (hT : ∀ b ∈ T, b ∈ signedIrr G)
    (hTortho : ∀ b ∈ T, ∀ b' ∈ T, cfInner b b' = if b = b' then 1 else 0)
    {D E : Set G} (hDE : Disjoint D E)
    (hΨconj : ∀ x, conj ((∑ b ∈ T, b) x) = -((∑ b ∈ T, b) x))
    (hΨE : ∀ x ∉ E, (∑ b ∈ T, b) x = 0)
    (hRD : ∀ a ∈ R, ∀ x ∉ D, a x - conj (a x) = 0) :
    ∀ a ∈ R, ∀ b ∈ T, cfInner a b = 0 := fun _ ha _ hb =>
  cfInner_eq_zero_of_conj_eq_neg_of_disjoint_support hR hT hTortho hDE hΨconj hΨE hRD ha hb

end CFSG.FeitThompson
