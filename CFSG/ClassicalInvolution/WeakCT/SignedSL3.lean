module

public import CFSG.Timmesfeld.ARS.FrameSL3Steinberg

public section

namespace CFSG.ClassicalInvolution.WeakCT

open scoped commutatorElement
open CFSG.Timmesfeld.ARS.FrameSL3

variable {F : Type} [Field F] {G : Type*} [Group G]

theorem map_neg_of_add {f : F → G} (hf : ∀ s t, f (s + t) = f s * f t) (s : F) :
    f (-s) = (f s)⁻¹ := by
  have h0 : f 0 = 1 := by
    have h := hf 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← hf, neg_add_cancel, h0]

theorem commutatorElement_swap_signed {x y z : F → G} (hz : ∀ s t, z (s + t) = z s * z t)
    {e : F → F → F} (h : ∀ s t, ⁅x s, y t⁆ = z (e s t)) (s t : F) :
    ⁅y s, x t⁆ = z (-(e t s)) := by
  rw [← commutatorElement_inv, h, map_neg_of_add hz]

theorem fam_comm_signed {a b c a' b' c' : F → G} (ha : ∀ s t, a (s + t) = a s * a t)
    (hb : ∀ s t, b (s + t) = b s * b t) (hc : ∀ s t, c (s + t) = c s * c t)
    (ha' : ∀ s t, a' (s + t) = a' s * a' t) (hb' : ∀ s t, b' (s + t) = b' s * b' t)
    (hc' : ∀ s t, c' (s + t) = c' s * c' t)
    (hac : ∀ s t, Commute (a s) (c t)) (hab' : ∀ s t, Commute (a s) (b' t))
    (hbc : ∀ s t, Commute (b s) (c t)) (hba' : ∀ s t, Commute (b s) (a' t))
    (ha'c' : ∀ s t, Commute (a' s) (c' t)) (hb'c' : ∀ s t, Commute (b' s) (c' t))
    (r₁ : ∀ s t, ⁅a s, b t⁆ = c (s * t)) (r₂ : ∀ s t, ⁅a' s, c t⁆ = b (s * t))
    (r₃ : ∀ s t, ⁅a s, c' t⁆ = b' (-(s * t))) (r₄ : ∀ s t, ⁅a' s, b' t⁆ = c' (-(s * t)))
    (r₅ : ∀ s t, ⁅b' s, c t⁆ = a (-(s * t))) (r₆ : ∀ s t, ⁅b s, c' t⁆ = a' (s * t)) :
    ∀ i j k l : Fin 3, i ≠ j → k ≠ l → ¬ (k = j ∧ l = i) → ∀ s t : F,
      ⁅fam a b c a' b' c' i j s, fam a b c a' b' c' k l t⁆ =
        if j = k then fam a b c a' b' c' i l (s * t)
        else if i = l then fam a b c a' b' c' k j (-(s * t)) else 1 := by
  have hcomm : ∀ {x y : F → G}, (∀ s t, Commute (x s) (y t)) →
      (∀ s t, ⁅x s, y t⁆ = 1) ∧ ∀ s t, ⁅y s, x t⁆ = 1 := fun h =>
    ⟨fun s t => commutatorElement_eq_one_iff_commute.2 (h s t),
      fun s t => commutatorElement_eq_one_iff_commute.2 (h t s).symm⟩
  have e₁ := hcomm hac
  have e₂ := hcomm hab'
  have e₃ := hcomm hbc
  have e₄ := hcomm hba'
  have e₅ := hcomm ha'c'
  have e₆ := hcomm hb'c'
  have s₁ : ∀ s t, ⁅b s, a t⁆ = c (-(s * t)) := fun s t => by
    rw [commutatorElement_swap_signed hc r₁ s t, mul_comm t s]
  have s₂ : ∀ s t, ⁅c s, a' t⁆ = b (-(s * t)) := fun s t => by
    rw [commutatorElement_swap_signed hb r₂ s t, mul_comm t s]
  have s₃ : ∀ s t, ⁅c' s, a t⁆ = b' (s * t) := fun s t => by
    rw [commutatorElement_swap_signed hb' r₃ s t, neg_neg, mul_comm t s]
  have s₄ : ∀ s t, ⁅b' s, a' t⁆ = c' (s * t) := fun s t => by
    rw [commutatorElement_swap_signed hc' r₄ s t, neg_neg, mul_comm t s]
  have s₅ : ∀ s t, ⁅c s, b' t⁆ = a (s * t) := fun s t => by
    rw [commutatorElement_swap_signed ha r₅ s t, neg_neg, mul_comm t s]
  have s₆ : ∀ s t, ⁅c' s, b t⁆ = a' (-(s * t)) := fun s t => by
    rw [commutatorElement_swap_signed ha' r₆ s t, mul_comm t s]
  intro i j k l hij hkl hex s t
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [fam] at hij hkl hex ⊢
  all_goals first
    | exact commutatorElement_eq_one_of_add ha s t | exact commutatorElement_eq_one_of_add hb s t
    | exact commutatorElement_eq_one_of_add hc s t | exact commutatorElement_eq_one_of_add ha' s t
    | exact commutatorElement_eq_one_of_add hb' s t | exact commutatorElement_eq_one_of_add hc' s t
    | exact e₁.1 s t | exact e₁.2 s t | exact e₂.1 s t | exact e₂.2 s t
    | exact e₃.1 s t | exact e₃.2 s t | exact e₄.1 s t | exact e₄.2 s t
    | exact e₅.1 s t | exact e₅.2 s t | exact e₆.1 s t | exact e₆.2 s t
    | exact r₁ s t | exact r₂ s t | exact r₃ s t | exact r₄ s t | exact r₅ s t | exact r₆ s t
    | exact s₁ s t | exact s₂ s t | exact s₃ s t | exact s₄ s t | exact s₅ s t | exact s₆ s t

end CFSG.ClassicalInvolution.WeakCT
