module

public import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic.Group
public import Mathlib.Basic.Finite.Sum

public section

namespace CFSG.KS.IndexTwo

variable {G : Type*} [Group G]

def twoSet (T : Subgroup G) (t : G) : Set G := {g | g ∈ T ∨ g * t⁻¹ ∈ T}

def twoSub (T : Subgroup G) (t : G) (hconj : ∀ h ∈ T, t * h * t⁻¹ ∈ T) (ht2 : t * t ∈ T) :
    Subgroup G where
  carrier := twoSet T t
  one_mem' := Or.inl T.one_mem
  mul_mem' := by
    intro a b ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (T.mul_mem ha hb)
    · refine Or.inr ?_
      rw [mul_assoc]
      exact T.mul_mem ha hb
    · refine Or.inr ?_
      have e : a * b * t⁻¹ = (a * t⁻¹) * (t * b * t⁻¹) := by group
      rw [e]
      exact T.mul_mem ha (hconj b hb)
    · refine Or.inl ?_
      have e : a * b = (a * t⁻¹) * (t * (b * t⁻¹) * t⁻¹) * (t * t) := by group
      rw [e]
      exact T.mul_mem (T.mul_mem ha (hconj _ hb)) ht2
  inv_mem' := by
    intro a ha
    rcases ha with ha | ha
    · exact Or.inl (T.inv_mem ha)
    · refine Or.inr ?_
      have e : a⁻¹ * t⁻¹ = t * ((t * t)⁻¹ * (a * t⁻¹)⁻¹) * t⁻¹ := by group
      rw [e]
      exact hconj _ (T.mul_mem (T.inv_mem ht2) (T.inv_mem ha))

theorem card_twoSub_le [Finite G] (T : Subgroup G) (t : G) (hconj : ∀ h ∈ T, t * h * t⁻¹ ∈ T)
    (ht2 : t * t ∈ T) : Nat.card (twoSub T t hconj ht2) ≤ 2 * Nat.card T := by
  classical
  let f : twoSub T t hconj ht2 → T ⊕ T := fun g =>
    if h : (g : G) ∈ T then Sum.inl ⟨g, h⟩ else Sum.inr ⟨(g : G) * t⁻¹, g.2.resolve_left h⟩
  have hf : Function.Injective f := by
    intro a b hab
    by_cases ha : (a : G) ∈ T <;> by_cases hb : (b : G) ∈ T
    · simp only [f, ha, hb, dite_true, Sum.inl.injEq, Subtype.mk.injEq] at hab
      exact Subtype.ext hab
    · simp [f, ha, hb] at hab
    · simp [f, ha, hb] at hab
    · simp only [f, ha, hb, dite_false, Sum.inr.injEq, Subtype.mk.injEq, mul_left_inj] at hab
      exact Subtype.ext hab
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_sum] at this
  omega

theorem card_closure_le_two_mul [Finite G] (T : Subgroup G) (t : G) (S : Set G)
    (hS : ∀ s ∈ S, s ∈ T ∨ s * t⁻¹ ∈ T) (hconj : ∀ h ∈ T, t * h * t⁻¹ ∈ T) (ht2 : t * t ∈ T) :
    Nat.card (Subgroup.closure S) ≤ 2 * Nat.card T := by
  have hle : Subgroup.closure S ≤ twoSub T t hconj ht2 := (Subgroup.closure_le _).2 hS
  exact (Subgroup.card_le_of_le hle).trans (card_twoSub_le T t hconj ht2)

theorem conj_mem_of_gens (T : Subgroup G) (t : G) (s : Set G) (hT : T = Subgroup.closure s)
    (hs : ∀ x ∈ s, t * x * t⁻¹ ∈ T) : ∀ h ∈ T, t * h * t⁻¹ ∈ T := by
  intro h hh
  rw [hT] at hh
  induction hh using Subgroup.closure_induction with
  | mem x hx => exact hs x hx
  | one => simp
  | mul x y _ _ ihx ihy =>
    have e : t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
    rw [e]
    exact T.mul_mem ihx ihy
  | inv x _ ihx =>
    have e : t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
    rw [e]
    exact T.inv_mem ihx

end CFSG.KS.IndexTwo

end
