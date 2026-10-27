module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Group
public import Mathlib.Basic.Complex.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {L : Type*} [Group L] (K : Subgroup L)

private theorem extend_subtype_apply (θ : K → ℂ) (z : L) [Decidable (z ∈ K)] :
    Function.extend K.subtype θ 0 z = if h : z ∈ K then θ ⟨z, h⟩ else 0 := by
  by_cases h : z ∈ K
  · rw [dif_pos h]
    exact K.subtype_injective.extend_apply θ 0 ⟨z, h⟩
  · rw [dif_neg h]
    refine Function.extend_apply' _ _ _ ?_
    rintro ⟨a, rfl⟩
    exact h a.2

private theorem extend_subtype_one (θ : K → ℂ) :
    Function.extend K.subtype θ 0 (1 : L) = θ 1 :=
  K.subtype_injective.extend_apply θ 0 1

variable [Fintype L]

noncomputable def indClassFun (θ : K → ℂ) (y : L) : ℂ :=
  (Nat.card K : ℂ)⁻¹ * ∑ t : L, Function.extend K.subtype θ 0 (t⁻¹ * y * t)

theorem indClassFun_apply [DecidablePred (· ∈ K)] (θ : K → ℂ) (y : L) :
    indClassFun K θ y =
      (Nat.card K : ℂ)⁻¹ * ∑ t : L, if h : t⁻¹ * y * t ∈ K then θ ⟨t⁻¹ * y * t, h⟩ else 0 := by
  simp only [indClassFun, extend_subtype_apply]

theorem indClassFun_conj (θ : K → ℂ) (x y : L) :
    indClassFun K θ (x * y * x⁻¹) = indClassFun K θ y := by
  simp only [indClassFun]
  congr 1
  refine (Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun t => ?_).symm
  simp only [Equiv.coe_mulLeft]
  congr 1
  group

theorem indClassFun_one (θ : K → ℂ) :
    indClassFun K θ 1 = (Nat.card L : ℂ) / (Nat.card K : ℂ) * θ 1 := by
  have h1 : ∀ t : L, t⁻¹ * (1 : L) * t = 1 := fun t => by group
  simp only [indClassFun, h1, extend_subtype_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.card_eq_fintype_card]
  ring

theorem indClassFun_eq_zero_of_notMem [K.Normal] (θ : K → ℂ) {y : L} (hy : y ∉ K) :
    indClassFun K θ y = 0 := by
  classical
  have h : ∀ t : L, Function.extend K.subtype θ 0 (t⁻¹ * y * t) = 0 := by
    intro t
    rw [extend_subtype_apply, dif_neg]
    intro hmem
    have := ‹K.Normal›.conj_mem _ hmem t
    rw [show t * (t⁻¹ * y * t) * t⁻¹ = y by group] at this
    exact hy this
  rw [indClassFun, Finset.sum_congr rfl fun t _ => h t]
  simp

theorem indClassFun_add (θ ψ : K → ℂ) :
    indClassFun K (θ + ψ) = indClassFun K θ + indClassFun K ψ := by
  classical
  have key : ∀ z : L, Function.extend K.subtype (θ + ψ) 0 z
      = Function.extend K.subtype θ 0 z + Function.extend K.subtype ψ 0 z := by
    intro z
    rw [extend_subtype_apply, extend_subtype_apply, extend_subtype_apply]
    split <;> simp
  funext y
  simp only [indClassFun, key, Finset.sum_add_distrib, Pi.add_apply, mul_add]

theorem indClassFun_smul (c : ℂ) (θ : K → ℂ) :
    indClassFun K (c • θ) = c • indClassFun K θ := by
  classical
  have key : ∀ z : L, Function.extend K.subtype (c • θ) 0 z
      = c * Function.extend K.subtype θ 0 z := by
    intro z
    rw [extend_subtype_apply, extend_subtype_apply]
    split <;> simp
  funext y
  simp only [indClassFun, key, ← Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  ring

@[simp] theorem indClassFun_zero : indClassFun K (0 : K → ℂ) = 0 := by
  funext y
  simp [indClassFun, Function.extend_zero]

noncomputable def indFam (X : Set (K → ℂ)) : Set (L → ℂ) := indClassFun K '' X

theorem mem_indFam {X : Set (K → ℂ)} {f : L → ℂ} :
    f ∈ indFam K X ↔ ∃ θ ∈ X, indClassFun K θ = f := Iff.rfl

theorem indClassFun_mem_indFam {X : Set (K → ℂ)} {θ : K → ℂ} (hθ : θ ∈ X) :
    indClassFun K θ ∈ indFam K X := ⟨θ, hθ, rfl⟩

theorem indFam_mono {X Y : Set (K → ℂ)} (h : X ⊆ Y) : indFam K X ⊆ indFam K Y :=
  Set.image_mono h

@[simp] theorem indFam_empty : indFam K (∅ : Set (K → ℂ)) = ∅ := Set.image_empty _

@[simp] theorem indFam_singleton (θ : K → ℂ) : indFam K {θ} = {indClassFun K θ} :=
  Set.image_singleton

theorem indFam_union (X Y : Set (K → ℂ)) : indFam K (X ∪ Y) = indFam K X ∪ indFam K Y :=
  Set.image_union _ _ _

theorem indFam_finite {X : Set (K → ℂ)} (hX : X.Finite) : (indFam K X).Finite := hX.image _

theorem conj_eq_of_mem_indFam {X : Set (K → ℂ)} {f : L → ℂ} (hf : f ∈ indFam K X) (x y : L) :
    f (x * y * x⁻¹) = f y := by
  obtain ⟨θ, -, rfl⟩ := hf
  exact indClassFun_conj K θ x y

theorem eq_zero_of_mem_indFam_of_notMem [K.Normal] {X : Set (K → ℂ)} {f : L → ℂ}
    (hf : f ∈ indFam K X) {y : L} (hy : y ∉ K) : f y = 0 := by
  obtain ⟨θ, -, rfl⟩ := hf
  exact indClassFun_eq_zero_of_notMem K θ hy

end CFSG.FeitThompson
