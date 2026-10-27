module

public import CFSG.FeitThompson.Representations.DisjointCoherentRowColumnContradiction
import Mathlib.Combinatorics.Matroid.Init

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module
open scoped ComplexConjugate

variable {G : Type*} [Group G]

section CrossedArray

variable {I J : Type*} [Fintype I] [Fintype J]

omit [Group G] in
open scoped Classical in
theorem cfInner_smul_sum_sub_smul_sub_eq [Fintype G] {η : I → J → (G → ℂ)} {ρ lam : G → ℂ}
    (hηortho : ∀ i j i' j', cfInner (η i j) (η i' j') = if i = i' ∧ j = j' then 1 else 0)
    (hρη : ∀ i j, cfInner ρ (η i j) = 0) (hlamη : ∀ i j, cfInner lam (η i j) = 0)
    (hρlam : cfInner ρ lam = 0) (i₀ : I) (j₀ : J) {δ ε : ℂ} (hε : ε = 1 ∨ ε = -1) (c : ℂ) :
    cfInner (δ • (∑ i, η i j₀) - c • ρ) (ε • (∑ j, η i₀ j) - lam) = δ * ε := by
  have hεconj : conj ε = ε := by rcases hε with rfl | rfl <;> simp
  have hηlam : ∀ i j, cfInner (η i j) lam = 0 := fun i j => by
    rw [← conj_cfInner, hlamη, map_zero]
  have hAB : cfInner (∑ i, η i j₀) (∑ j, η i₀ j) = 1 := by
    rw [cfInner_sum_left]
    simp only [cfInner_sum_right]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hηortho i j₀ i₀ j]
    simp only [ite_and]
    simp
  have hAlam : cfInner (∑ i, η i j₀) lam = 0 := by rw [cfInner_sum_left]; simp [hηlam]
  have hρB : cfInner ρ (∑ j, η i₀ j) = 0 := by rw [cfInner_sum_right]; simp [hρη]
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right,
    cfInner_smul_left δ _ (ε • (∑ j, η i₀ j)), cfInner_smul_left δ _ lam,
    cfInner_smul_left c _ (ε • (∑ j, η i₀ j)), cfInner_smul_left c _ lam,
    cfInner_smul_right, cfInner_smul_right, hAB, hAlam, hρB, hρlam, hεconj]
  ring

open scoped Classical in
theorem cfInner_smul_sum_sub_smul_sub_ne_zero [Fintype G] {η : I → J → (G → ℂ)} {ρ lam : G → ℂ}
    (hηortho : ∀ i j i' j', cfInner (η i j) (η i' j') = if i = i' ∧ j = j' then 1 else 0)
    (hρ : ρ ∈ signedIrr G) (hlam : lam ∈ signedIrr G)
    (hlamne : lam ≠ fun x => conj (lam x))
    (hρη : ∀ i j, cfInner ρ (η i j) = 0) (hlamη : ∀ i j, cfInner lam (η i j) = 0)
    {D E : Set G} (hDE : Disjoint D E)
    (hρD : ∀ x ∉ D, ρ x - conj (ρ x) = 0) (hlamE : ∀ x ∉ E, lam x - conj (lam x) = 0)
    (i₀ : I) (j₀ : J) {δ ε : ℂ} (hδ : δ = 1 ∨ δ = -1) (hε : ε = 1 ∨ ε = -1) (c : ℂ) :
    cfInner (δ • (∑ i, η i j₀) - c • ρ) (ε • (∑ j, η i₀ j) - lam) = δ * ε ∧ δ * ε ≠ 0 := by
  refine ⟨cfInner_smul_sum_sub_smul_sub_eq hηortho hρη hlamη
    (cfInner_eq_zero_of_disjoint_support_of_ne_conj hρ hlam hlamne hDE hρD hlamE) i₀ j₀ hε c, ?_⟩
  rcases hδ with rfl | rfl <;> rcases hε with rfl | rfl <;> norm_num

open scoped Classical in
theorem not_vanishes_outside_of_crossed_array [Fintype G] {η : I → J → (G → ℂ)} {ρ lam : G → ℂ}
    (hηortho : ∀ i j i' j', cfInner (η i j) (η i' j') = if i = i' ∧ j = j' then 1 else 0)
    (hρ : ρ ∈ signedIrr G) (hlam : lam ∈ signedIrr G)
    (hlamne : lam ≠ fun x => conj (lam x))
    (hρη : ∀ i j, cfInner ρ (η i j) = 0) (hlamη : ∀ i j, cfInner lam (η i j) = 0)
    {D E : Set G} (hDE : Disjoint D E)
    (hρD : ∀ x ∉ D, ρ x - conj (ρ x) = 0) (hlamE : ∀ x ∉ E, lam x - conj (lam x) = 0)
    (i₀ : I) (j₀ : J) {δ ε : ℂ} (hδ : δ = 1 ∨ δ = -1) (hε : ε = 1 ∨ ε = -1) (c : ℂ) :
    ¬ ((∀ x ∉ D, (δ • (∑ i, η i j₀) - c • ρ) x = 0) ∧
      (∀ x ∉ E, (ε • (∑ j, η i₀ j) - lam) x = 0)) := by
  rintro ⟨hf, hg⟩
  obtain ⟨hval, hne⟩ := cfInner_smul_sum_sub_smul_sub_ne_zero hηortho hρ hlam hlamne hρη hlamη
    hDE hρD hlamE i₀ j₀ hδ hε c
  refine hne ?_
  rw [← hval]
  refine cfInner_eq_zero_of_disjoint_support (Set.disjoint_left.2 fun x hx hy => ?_)
  have hxD : x ∈ D := by by_contra h; exact hx (hf x h)
  have hxE : x ∈ E := by by_contra h; exact hy (hg x h)
  exact Set.disjoint_left.1 hDE hxD hxE

end CrossedArray

end CFSG.FeitThompson
