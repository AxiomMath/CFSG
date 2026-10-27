module

public import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.Basic
import Mathlib.GroupTheory.IsPerfect
public import CFSG.ClassicalGroups.Orthogonal.Perfect
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap
open scoped commutatorElement

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

variable (Q) in
noncomputable def reflect (v : V) : V ≃ₗ[K] V :=
  open scoped Classical in
  if h : Q v ≠ 0 then
    @TauCeti.QuadraticMap.reflection K V _ _ _ Q v (invertibleOfNonzero h)
  else 1

theorem reflect_eq_reflection {v : V} [Invertible (Q v)] :
    reflect Q v = TauCeti.QuadraticMap.reflection Q v := by
  have h : Q v ≠ 0 := (isUnit_of_invertible (Q v)).ne_zero
  rw [reflect, dite_eq_left h]
  congr 1
  exact Subsingleton.elim _ _

theorem reflect_apply {v : V} (hv : Q v ≠ 0) (x : V) :
    reflect Q v x = x - (polar Q v x / Q v) • v := by
  let _ : Invertible (Q v) := invertibleOfNonzero hv
  rw [reflect_eq_reflection, TauCeti.QuadraticMap.reflection_apply_eq_sub_div]

theorem reflect_of_map_eq_zero {v : V} (hv : Q v = 0) : reflect Q v = 1 := by
  rw [reflect, dite_eq_right (not_not.mpr hv)]

variable (Q) in
theorem reflect_mem_orthogonalGroup (v : V) :
    reflect Q v ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  by_cases hv : Q v = 0
  · rw [reflect_of_map_eq_zero hv]
    exact Subgroup.one_mem _
  · let _ : Invertible (Q v) := invertibleOfNonzero hv
    rw [reflect_eq_reflection]
    exact TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q v

variable (Q) in
theorem reflect_mul_self (v : V) : reflect Q v * reflect Q v = 1 := by
  by_cases hv : Q v = 0
  · rw [reflect_of_map_eq_zero hv, one_mul]
  · let _ : Invertible (Q v) := invertibleOfNonzero hv
    rw [reflect_eq_reflection]
    exact TauCeti.QuadraticMap.reflection_mul_self Q v

variable (Q) in
theorem reflect_inv (v : V) : (reflect Q v)⁻¹ = reflect Q v :=
  inv_eq_of_mul_eq_one_left (reflect_mul_self Q v)

theorem reflect_conj {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (v : V) :
    g * reflect Q v * g⁻¹ = reflect Q (g v) := by
  by_cases hv : Q v = 0
  · rw [reflect_of_map_eq_zero hv, reflect_of_map_eq_zero (by rw [map_of_mem hg, hv]), mul_one,
      mul_inv_cancel]
  · have hgv : Q (g v) ≠ 0 := by rwa [map_of_mem hg]
    refine LinearEquiv.ext fun x => ?_
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, reflect_apply hv, reflect_apply hgv,
      map_sub, map_smul, LinearEquiv.apply_inv_apply', map_of_mem hg, ← polar_map_of_mem hg v,
      LinearEquiv.apply_inv_apply']

theorem reflect_apply_of_polar_eq_zero {v x : V} (h : polar Q v x = 0) : reflect Q v x = x := by
  by_cases hv : Q v = 0
  · rw [reflect_of_map_eq_zero hv]
    rfl
  · rw [reflect_apply hv, h, zero_div, zero_smul, sub_zero]

theorem commutatorElement_reflect_mem (hQ : (polarBilin Q).Nondegenerate) {P P' : HypPair Q}
    (h : P.Orth P') (u v : V) : ⁅reflect Q u, reflect Q v⁆ ∈ elementaryGroup Q := by
  by_cases hv : Q v = 0
  · rw [reflect_of_map_eq_zero hv, commutatorElement_one_right]
    exact Subgroup.one_mem _
  have hv0 : v ≠ 0 := fun h0 => hv (by rw [h0, QuadraticMap.map_zero])
  have hsO := reflect_mem_orthogonalGroup Q u
  have hsv0 : reflect Q u v ≠ 0 := fun h0 => hv0 ((reflect Q u).map_eq_zero_iff.mp h0)
  obtain ⟨e, he, hev⟩ := exists_mem_elementaryGroup_apply_eq hQ h hv0 hsv0
    (by rw [map_of_mem hsO])
  have heO := elementaryGroup_le_orthogonalGroup Q he
  have h1 : reflect Q u * reflect Q v * (reflect Q u)⁻¹ = e * reflect Q v * e⁻¹ := by
    rw [reflect_conj hsO, reflect_conj heO, hev]
  rw [commutatorElement_def, h1, mul_assoc, mul_assoc]
  refine mul_mem he ?_
  have := conj_mem_elementaryGroup (reflect_mem_orthogonalGroup Q v) (inv_mem he)
  rwa [mul_assoc] at this

section GroupLemma

variable {G : Type*} [Group G]

private theorem commutatorElement_mem_of_mem_closure {N O : Subgroup G} {S : Set G}
    (hN : ∀ g ∈ O, ∀ x ∈ N, g * x * g⁻¹ ∈ N) (hcl : Subgroup.closure S ≤ O) {h : G}
    (hS : ∀ s ∈ S, ⁅s, h⁆ ∈ N) {g : G} (hg : g ∈ Subgroup.closure S) : ⁅g, h⁆ ∈ N := by
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact hS s hs
  | one => rw [commutatorElement_one_left]; exact N.one_mem
  | mul a b ha hb iha ihb =>
    have hid : ⁅a * b, h⁆ = a * ⁅b, h⁆ * a⁻¹ * ⁅a, h⁆ := by
      simp only [commutatorElement_def]
      group
    rw [hid]
    exact N.mul_mem (hN a (hcl ha) _ ihb) iha
  | inv a ha iha =>
    have hid : ⁅a⁻¹, h⁆ = a⁻¹ * ⁅a, h⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [hid]
    exact hN _ (hcl (inv_mem ha)) _ (N.inv_mem iha)

theorem commutator_le_of_le_closure {N O : Subgroup G} {S : Set G}
    (hN : ∀ g ∈ O, ∀ x ∈ N, g * x * g⁻¹ ∈ N) (hNO : N ≤ O) (hSO : S ⊆ O)
    (hO : O ≤ Subgroup.closure (S ∪ N)) (hS : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ ∈ N) : ⁅O, O⁆ ≤ N := by
  have hcl : Subgroup.closure (S ∪ N) ≤ O := by
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · exact hSO hx
    · exact hNO hx
  have hNcomm : ∀ g ∈ O, ∀ x ∈ N, ⁅g, x⁆ ∈ N ∧ ⁅x, g⁆ ∈ N := by
    intro g hg x hx
    have h1 : ⁅g, x⁆ ∈ N := by
      rw [commutatorElement_def]
      exact N.mul_mem (hN g hg x hx) (N.inv_mem hx)
    refine ⟨h1, ?_⟩
    rw [← commutatorElement_inv]
    exact N.inv_mem h1
  have step1 : ∀ t ∈ S ∪ N, ∀ g ∈ O, ⁅g, t⁆ ∈ N := by
    rintro t (ht | ht) g hg
    · refine commutatorElement_mem_of_mem_closure hN hcl ?_ (hO hg)
      rintro s (hs | hs)
      · exact hS s hs t ht
      · exact (hNcomm t (hSO ht) s hs).2
    · exact (hNcomm g hg t ht).1
  rw [Subgroup.commutator_le]
  intro h hh g hg
  refine commutatorElement_mem_of_mem_closure hN hcl ?_ (hO hh)
  intro t ht
  rw [← commutatorElement_inv]
  exact N.inv_mem (step1 t ht g hg)

end GroupLemma

theorem commutator_orthogonalGroup_eq_of_le_closure (hQ : (polarBilin Q).Nondegenerate)
    {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃)
    (hgen : TauCeti.QuadraticMap.orthogonalGroup Q ≤
      Subgroup.closure (Set.range (reflect Q) ∪ elementaryGroup Q)) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q := by
  apply le_antisymm
  · refine commutator_le_of_le_closure (fun g hg x hx => conj_mem_elementaryGroup hg hx)
      (elementaryGroup_le_orthogonalGroup Q) ?_ hgen ?_
    · rintro _ ⟨v, rfl⟩
      exact reflect_mem_orthogonalGroup Q v
    · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
      exact commutatorElement_reflect_mem hQ h₁₂ u v
  · have hperf : Group.IsPerfect (elementaryGroup Q) :=
      Group.isPerfect_def.mpr (commutator_elementaryGroup_eq_top h₁₂ h₁₃ h₂₃ hQ)
    calc elementaryGroup Q = ⁅elementaryGroup Q, elementaryGroup Q⁆ :=
          (Subgroup.commutator_eq_self).symm
      _ ≤ _ := Subgroup.commutator_mono (elementaryGroup_le_orthogonalGroup Q)
        (elementaryGroup_le_orthogonalGroup Q)

theorem orthogonalGroup_le_closure_reflect [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) :
    TauCeti.QuadraticMap.orthogonalGroup Q ≤ Subgroup.closure (Set.range (reflect Q)) := by
  have : NeZero (2 : K) := ⟨h2⟩
  let _ : Invertible (2 : K) := invertibleOfNonzero h2
  have hQ' : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  have htop := TauCeti.QuadraticMap.subgroup_eq_top_of_reflection_mem Q hQ'
    ((Subgroup.closure (Set.range (reflect Q))).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup Q))
    (fun v _ => by
      rw [Subgroup.mem_subgroupOf, TauCeti.QuadraticMap.coe_reflectionOrthogonal,
        ← reflect_eq_reflection]
      exact Subgroup.subset_closure ⟨v, rfl⟩)
  intro g hg
  have : (⟨g, hg⟩ : TauCeti.QuadraticMap.orthogonalGroup Q) ∈
      (Subgroup.closure (Set.range (reflect Q))).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    rw [htop]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

theorem commutator_orthogonalGroup_eq_elementaryGroup_of_two_ne_zero [FiniteDimensional K V]
    (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate) {P₁ P₂ P₃ : HypPair Q}
    (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q :=
  commutator_orthogonalGroup_eq_of_le_closure hQ h₁₂ h₁₃ h₂₃
    ((orthogonalGroup_le_closure_reflect h2 hQ).trans
      (Subgroup.closure_mono Set.subset_union_left))

end CFSG.ClassicalGroups.Orthogonal
