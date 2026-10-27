module

public import CFSG.ClassicalInvolution.TwoGroupCase.Q8
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.ClassicalInvolution

open QuaternionGroup

private def q8E {H : Type*} [Group H] (u v : H) : QuaternionGroup 2 → H
  | .a k => u ^ k.val
  | .xa k => v * u ^ k.val

private theorem q8E_eq {H : Type*} [Group H] (f : QuaternionGroup 2 →* H) (x : QuaternionGroup 2) :
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

private def Q8AP (u v : QuaternionGroup 2) : Prop :=
  (∀ x y, q8E u v (x * y) = q8E u v x * q8E u v y) ∧
    ∀ x y, q8E u v x = q8E u v y → x = y

private instance (u v : QuaternionGroup 2) : Decidable (Q8AP u v) := by
  unfold Q8AP; infer_instance

private theorem q8AP_of_mulAut (β : MulAut (QuaternionGroup 2)) :
    Q8AP (β (a 1)) (β (xa 0)) := by
  have e : ∀ x, β x = q8E (β (a 1)) (β (xa 0)) x := fun x => q8E_eq β.toMonoidHom x
  refine ⟨fun x y => ?_, fun x y h => β.injective ?_⟩
  · rw [← e, ← e, ← e, map_mul]
  · rw [e x, e y]; exact h

private theorem q8_check_transitive : ∀ u v : QuaternionGroup 2, Q8AP u v →
    (∃ x, q8E u v x ≠ x) → (∀ x, q8E u v (q8E u v (q8E u v x)) = x) →
    ∀ g h : QuaternionGroup 2, g ^ 2 ≠ 1 → g ^ 4 = 1 → h ^ 2 ≠ 1 → h ^ 4 = 1 →
      (g = h ∨ g = h⁻¹) ∨ (q8E u v g = h ∨ q8E u v g = h⁻¹) ∨
        (q8E u v (q8E u v g) = h ∨ q8E u v (q8E u v g) = h⁻¹) := by
  decide +kernel

private theorem q8_check_three : ∀ u₁ v₁ : QuaternionGroup 2, Q8AP u₁ v₁ →
    ∀ u₂ v₂ : QuaternionGroup 2, Q8AP u₂ v₂ →
    (q8E u₁ v₁ (a 1) = xa 0 ∨ q8E u₁ v₁ (a 1) = (xa 0)⁻¹) →
    (q8E u₂ v₂ (a 1) = xa 1 ∨ q8E u₂ v₂ (a 1) = (xa 1)⁻¹) →
    ((∃ x, q8E u₁ v₁ x ≠ x) ∧ ∀ x, q8E u₁ v₁ (q8E u₁ v₁ (q8E u₁ v₁ x)) = x) ∨
    ((∃ x, q8E u₂ v₂ x ≠ x) ∧ ∀ x, q8E u₂ v₂ (q8E u₂ v₂ (q8E u₂ v₂ x)) = x) ∨
    ((∃ x, q8E u₁ v₁ (q8E u₂ v₂ x) ≠ x) ∧
      ∀ x, q8E u₁ v₁ (q8E u₂ v₂ (q8E u₁ v₁ (q8E u₂ v₂
        (q8E u₁ v₁ (q8E u₂ v₂ x))))) = x) := by
  decide +kernel

private theorem q8E_apply (φ : MulAut (QuaternionGroup 2)) (x : QuaternionGroup 2) :
    q8E (φ (a 1)) (φ (xa 0)) x = φ x :=
  (q8E_eq φ.toMonoidHom x).symm

theorem q8_aut_transitive {φ : MulAut (QuaternionGroup 2)} (h3 : φ ^ 3 = 1) (h1 : φ ≠ 1)
    {g h : QuaternionGroup 2} (hg2 : g ^ 2 ≠ 1) (hg4 : g ^ 4 = 1) (hh2 : h ^ 2 ≠ 1)
    (hh4 : h ^ 4 = 1) :
    ∃ m : ℕ, m < 3 ∧ ((φ ^ m) g = h ∨ (φ ^ m) g = h⁻¹) := by
  have hne : ∃ x, φ x ≠ x := by
    by_contra hcon
    push Not at hcon
    exact h1 (MulEquiv.ext fun x => by simpa using hcon x)
  have hcube : ∀ x, φ (φ (φ x)) = x := fun x => by
    have := congrArg (fun γ : MulAut (QuaternionGroup 2) => γ x) h3
    simpa [pow_succ, MulAut.mul_apply] using this
  have key := q8_check_transitive (φ (a 1)) (φ (xa 0)) (q8AP_of_mulAut φ)
    (by simpa only [q8E_apply] using hne) (by simpa only [q8E_apply] using hcube) g h hg2
    hg4 hh2 hh4
  simp only [q8E_apply] at key
  rcases key with h0 | h0 | h0
  · exact ⟨0, by norm_num, by simpa using h0⟩
  · exact ⟨1, by norm_num, by simpa using h0⟩
  · exact ⟨2, by norm_num, by simpa [pow_two, MulAut.mul_apply] using h0⟩

theorem q8_aut_three {φ₁ φ₂ : MulAut (QuaternionGroup 2)}
    (h₁ : φ₁ (a 1) = xa 0 ∨ φ₁ (a 1) = (xa 0)⁻¹)
    (h₂ : φ₂ (a 1) = xa 1 ∨ φ₂ (a 1) = (xa 1)⁻¹) :
    (φ₁ ≠ 1 ∧ φ₁ ^ 3 = 1) ∨ (φ₂ ≠ 1 ∧ φ₂ ^ 3 = 1) ∨ (φ₁ * φ₂ ≠ 1 ∧ (φ₁ * φ₂) ^ 3 = 1) := by
  have conv : ∀ ψ : MulAut (QuaternionGroup 2), (∃ x, ψ x ≠ x) → (∀ x, ψ (ψ (ψ x)) = x) →
      ψ ≠ 1 ∧ ψ ^ 3 = 1 := by
    rintro ψ ⟨x, hx⟩ hc
    refine ⟨fun h => hx (by simp [h]), MulEquiv.ext fun y => ?_⟩
    simpa [pow_succ, MulAut.mul_apply] using hc y
  have key := q8_check_three (φ₁ (a 1)) (φ₁ (xa 0)) (q8AP_of_mulAut φ₁) (φ₂ (a 1)) (φ₂ (xa 0))
    (q8AP_of_mulAut φ₂) (by simpa only [q8E_apply] using h₁)
    (by simpa only [q8E_apply] using h₂)
  simp only [q8E_apply] at key
  rcases key with ⟨hn, hc⟩ | ⟨hn, hc⟩ | ⟨hn, hc⟩
  · exact Or.inl (conv φ₁ hn hc)
  · exact Or.inr (Or.inl (conv φ₂ hn hc))
  · exact Or.inr (Or.inr (conv (φ₁ * φ₂) (by simpa [MulAut.mul_apply] using hn)
      (fun x => by simpa [MulAut.mul_apply] using hc x)))

end CFSG.ClassicalInvolution
