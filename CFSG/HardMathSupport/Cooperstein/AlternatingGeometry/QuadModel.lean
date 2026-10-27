module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.BlockWreath

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

@[expose] def d8 : Subgroup (Perm (Fin 4)) where
  carrier := {σ | ∀ x y : Fin 4, (σ x).val / 2 = (σ y).val / 2 ↔ x.val / 2 = y.val / 2}
  mul_mem' := by
    have h : ∀ a b : Perm (Fin 4),
        (∀ x y : Fin 4, (a x).val / 2 = (a y).val / 2 ↔ x.val / 2 = y.val / 2) →
        (∀ x y : Fin 4, (b x).val / 2 = (b y).val / 2 ↔ x.val / 2 = y.val / 2) →
        (∀ x y : Fin 4, ((a * b) x).val / 2 = ((a * b) y).val / 2 ↔ x.val / 2 = y.val / 2) := by
      decide
    exact fun {a b} ha hb => h a b ha hb
  one_mem' := fun _ _ => Iff.rfl
  inv_mem' := by
    have h : ∀ a : Perm (Fin 4),
        (∀ x y : Fin 4, (a x).val / 2 = (a y).val / 2 ↔ x.val / 2 = y.val / 2) →
        (∀ x y : Fin 4, (a⁻¹ x).val / 2 = (a⁻¹ y).val / 2 ↔ x.val / 2 = y.val / 2) := by
      decide
    exact fun {a} ha => h a ha

theorem mem_d8 {σ : Perm (Fin 4)} :
    σ ∈ d8 ↔ ∀ x y : Fin 4, (σ x).val / 2 = (σ y).val / 2 ↔ x.val / 2 = y.val / 2 := Iff.rfl

theorem wreathHyp_d8 : WreathHyp d8 where
  pgroup := by
    intro g
    refine ⟨2, ?_⟩
    have h : ∀ a : Perm (Fin 4),
        (∀ x y : Fin 4, (a x).val / 2 = (a y).val / 2 ↔ x.val / 2 = y.val / 2) → a ^ 4 = 1 := by
      decide
    apply Subtype.ext
    simpa using h g.1 g.2
  trans := by
    have h : ∀ a b : Fin 4, ∃ d : Perm (Fin 4),
        (∀ x y : Fin 4, (d x).val / 2 = (d y).val / 2 ↔ x.val / 2 = y.val / 2) ∧ d a = b := by
      decide
    intro a b
    obtain ⟨d, hd, hdab⟩ := h a b
    exact ⟨d, hd, hdab⟩
  odd := by
    have h : (swap (0 : Fin 4) 1) ∈ d8 ∧ sign (swap (0 : Fin 4) 1) = -1 := by
      refine ⟨?_, sign_swap (by decide)⟩
      show ∀ x y : Fin 4, ((swap (0 : Fin 4) 1) x).val / 2 = ((swap (0 : Fin 4) 1) y).val / 2 ↔
        x.val / 2 = y.val / 2
      decide
    exact ⟨_, h.1, h.2⟩
  selfNorm := by
    have h : ∀ s : Perm (Fin 4),
        (∀ d : Perm (Fin 4),
          (∀ x y : Fin 4, (d x).val / 2 = (d y).val / 2 ↔ x.val / 2 = y.val / 2) →
          (∀ x y : Fin 4, ((s * d * s⁻¹) x).val / 2 = ((s * d * s⁻¹) y).val / 2 ↔
            x.val / 2 = y.val / 2)) →
        (∀ x y : Fin 4, (s x).val / 2 = (s y).val / 2 ↔ x.val / 2 = y.val / 2) := by
      decide
    intro s hs
    exact h s (fun d hd => hs d hd)

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
