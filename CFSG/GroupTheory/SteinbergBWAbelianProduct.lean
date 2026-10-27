module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory.ZJ

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

theorem commutatorElement_mem_of_closure {T : Set G} {N : Subgroup G}
    (hN : ∀ n ∈ N, ∀ h ∈ closure T, n * h = h * n) (hT : ∀ s ∈ T, ∀ t ∈ T, ⁅s, t⁆ ∈ N)
    {x y : G} (hx : x ∈ closure T) (hy : y ∈ closure T) : ⁅x, y⁆ ∈ N := by
  have hconj : ∀ n ∈ N, ∀ h ∈ closure T, h * n * h⁻¹ = n := fun n hn h hh => by
    rw [← hN n hn h hh, mul_inv_cancel_right]
  have hleft : ∀ s ∈ T, ∀ y ∈ closure T, ⁅s, y⁆ ∈ N := by
    intro s hs y hy
    induction hy using Subgroup.closure_induction with
    | mem t ht => exact hT s hs t ht
    | one => rw [commutatorElement_one_right]; exact N.one_mem
    | mul y₁ y₂ hy₁ hy₂ h₁ h₂ =>
      have e : ⁅s, y₁ * y₂⁆ = ⁅s, y₁⁆ * (y₁ * ⁅s, y₂⁆ * y₁⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e, hconj _ h₂ _ hy₁]
      exact N.mul_mem h₁ h₂
    | inv y hy h =>
      have e : ⁅s, y⁻¹⁆ = y⁻¹ * ⁅s, y⁆⁻¹ * y⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e, hconj _ (N.inv_mem h) _ (inv_mem hy)]
      exact N.inv_mem h
  induction hx using Subgroup.closure_induction generalizing y with
  | mem s hs => exact hleft s hs y hy
  | one => rw [commutatorElement_one_left]; exact N.one_mem
  | mul x₁ x₂ hx₁ hx₂ h₁ h₂ =>
    have e : ⁅x₁ * x₂, y⁆ = x₁ * ⁅x₂, y⁆ * x₁⁻¹ * ⁅x₁, y⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e, hconj _ (h₂ hy) _ hx₁]
    exact N.mul_mem (h₂ hy) (h₁ hy)
  | inv x hx h =>
    have e : ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, hconj _ (N.inv_mem (h hy)) _ (inv_mem hx)]
    exact N.inv_mem (h hy)

theorem mutually_normalizing_abelian_product {A D : Subgroup G} (hA : IsMulCommutative A)
    (hD : IsMulCommutative D) (hAD : A ≤ normalizer (D : Set G))
    (hDA : D ≤ normalizer (A : Set G)) :
    ((A ⊔ D : Subgroup G) : Set G) = (A : Set G) * (D : Set G) ∧ ⁅A ⊔ D, A ⊔ D⁆ ≤ A ⊓ D ∧
      A ⊓ D ≤ (center (A ⊔ D : Subgroup G)).map (A ⊔ D).subtype := by
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hD.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcent : A ⊔ D ≤ centralizer ((A ⊓ D : Subgroup G) : Set G) := by
    refine sup_le (fun a ha => ?_) (fun d hd => ?_)
    · exact mem_centralizer_iff.mpr fun n hn => hAc n hn.1 a ha
    · exact mem_centralizer_iff.mpr fun n hn => hDc n hn.2 d hd
  have hN : ∀ n ∈ A ⊓ D, ∀ h ∈ A ⊔ D, n * h = h * n := fun n hn h hh =>
    mem_centralizer_iff.mp (hcent hh) n hn
  have hcross : ∀ a ∈ A, ∀ d ∈ D, ⁅a, d⁆ ∈ A ⊓ D := by
    intro a ha d hd
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc d]
      exact A.mul_mem ha ((mem_normalizer_iff.mp (hDA hd) a⁻¹).mp (A.inv_mem ha))
    · rw [commutatorElement_def]
      exact D.mul_mem ((mem_normalizer_iff.mp (hAD ha) d).mp hd) (D.inv_mem hd)
  have hsup : A ⊔ D = closure ((A : Set G) ∪ D) := by
    rw [closure_union, closure_eq, closure_eq]
  refine ⟨coe_mul_of_left_le_normalizer_right A D hAD, ?_, ?_⟩
  · rw [commutator_le]
    intro x hx y hy
    rw [hsup] at hx hy
    refine commutatorElement_mem_of_closure (fun n hn h hh => hN n hn h (hsup ▸ hh)) ?_ hx hy
    rintro s (hs | hs) t (ht | ht)
    · rw [(commutatorElement_eq_one_iff_mul_comm).mpr (hAc s hs t ht)]
      exact (A ⊓ D).one_mem
    · exact hcross s hs t ht
    · rw [← commutatorElement_inv]
      exact (A ⊓ D).inv_mem (hcross t ht s hs)
    · rw [(commutatorElement_eq_one_iff_mul_comm).mpr (hDc s hs t ht)]
      exact (A ⊓ D).one_mem
  · intro x hx
    refine ⟨⟨x, mem_sup_left hx.1⟩, mem_center_iff.mpr fun h => Subtype.ext ?_, rfl⟩
    exact (hN x hx h h.2).symm

end CFSG.GroupTheory.ZJ
