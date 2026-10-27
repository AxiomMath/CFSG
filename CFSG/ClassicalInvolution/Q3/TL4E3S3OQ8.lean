module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3O

open QuaternionGroup

@[expose] def q8E {H : Type*} [Group H] (u v : H) : QuaternionGroup 2 → H
  | .a k => u ^ k.val
  | .xa k => v * u ^ k.val

theorem q8E_eq {H : Type*} [Group H] (f : QuaternionGroup 2 →* H) (x : QuaternionGroup 2) :
    f x = q8E (f (a 1)) (f (xa 0)) x := by
  have ha : ∀ k : ZMod 4, (a k : QuaternionGroup 2) = (a 1) ^ k.val := fun k => by
    rw [a_one_pow, ZMod.natCast_zmod_val]
  cases x with
  | a k =>
    calc f (a k) = f ((a 1) ^ k.val) := by rw [ha k]
      _ = (f (a 1)) ^ k.val := map_pow _ _ _
  | xa k =>
    have h : (xa k : QuaternionGroup 2) = xa 0 * a k := by simp
    calc f (xa k) = f (xa 0) * f ((a 1) ^ k.val) := by rw [h, map_mul, ha k]
      _ = f (xa 0) * (f (a 1)) ^ k.val := by rw [map_pow]

@[expose] def Q8Pair (u v : QuaternionGroup 2) : Prop :=
  (∀ x y, q8E u v (x * y) = q8E u v x * q8E u v y) ∧ ∀ x y, q8E u v x = q8E u v y → x = y

instance (u v : QuaternionGroup 2) : Decidable (Q8Pair u v) := by
  unfold Q8Pair
  infer_instance

theorem q8Pair_of_mulEquiv (β : QuaternionGroup 2 ≃* QuaternionGroup 2) :
    Q8Pair (β (a 1)) (β (xa 0)) := by
  have e : ∀ x, β x = q8E (β (a 1)) (β (xa 0)) x := fun x => q8E_eq β.toMonoidHom x
  refine ⟨fun x y => ?_, fun x y h => β.injective ?_⟩
  · rw [← e, ← e, ← e, map_mul]
  · rw [e x, e y]
    exact h

theorem q8_pow_four : ∀ x : QuaternionGroup 2, x ^ 4 = 1 := by
  decide

private theorem q8_sq_aux : ∀ u v : QuaternionGroup 2, Q8Pair u v →
    (∀ x, q8E u v (q8E u v (q8E u v (q8E u v x))) = x) → (∃ x, q8E u v (q8E u v x) ≠ x) →
    ∃ g : QuaternionGroup 2, g * g ≠ 1 ∧ ∀ x, q8E u v (q8E u v x) = g * x * g⁻¹ := by
  decide +kernel

theorem q8_sq_inner (γ : QuaternionGroup 2 ≃* QuaternionGroup 2)
    (h4 : ∀ x, γ (γ (γ (γ x))) = x) (h2 : ∃ x, γ (γ x) ≠ x) :
    ∃ g : QuaternionGroup 2, g * g ≠ 1 ∧ ∀ x, γ (γ x) = g * x * g⁻¹ := by
  have e : ∀ x, γ x = q8E (γ (a 1)) (γ (xa 0)) x := fun x => q8E_eq γ.toMonoidHom x
  obtain ⟨g, hg, hgx⟩ := q8_sq_aux _ _ (q8Pair_of_mulEquiv γ)
    (fun x => by rw [← e, ← e, ← e, ← e]; exact h4 x)
    (by
      obtain ⟨x, hx⟩ := h2
      exact ⟨x, by rw [← e, ← e]; exact hx⟩)
  exact ⟨g, hg, fun x => by rw [e (γ x), e x]; exact hgx x⟩

end CFSG.ClassicalInvolution.Q3.TL4.E3S3O
