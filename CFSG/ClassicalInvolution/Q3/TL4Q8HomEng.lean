module

public import CFSG.ClassicalInvolution.Q3.Q3TLT3Q8

public section
namespace CFSG.ClassicalInvolution.Q3.TL4
open CFSG CFSG.ClassicalInvolution
open QuaternionGroup

theorem E3.q8_hom_eq_one_of_aut3_gen {A : Type*} [CommGroup A] (f : QuaternionGroup 2 →* A)
    {φ : MulAut (QuaternionGroup 2)} (h3 : φ ^ 3 = 1) (h1 : φ ≠ 1)
    (hf : ∀ y, f (φ y) = f y) (y : QuaternionGroup 2) : f y = 1 := by
  have hpow : ∀ m : ℕ, ∀ y, f ((φ ^ m) y) = f y := by
    intro m
    induction m with
    | zero => intro y; rfl
    | succ m ih => intro y; rw [pow_succ', MulAut.mul_apply, hf, ih]
  have hsame : ∀ g h : QuaternionGroup 2, g ^ 2 ≠ 1 → g ^ 4 = 1 → h ^ 2 ≠ 1 → h ^ 4 = 1 →
      f g = f h ∨ f g = (f h)⁻¹ := by
    intro g h hg2 hg4 hh2 hh4
    obtain ⟨m, -, hm | hm⟩ := q8_aut_transitive h3 h1 hg2 hg4 hh2 hh4
    · exact Or.inl (by rw [← hpow m g, hm])
    · exact Or.inr (by rw [← hpow m g, hm, map_inv])
  have hinv : ∀ g k : QuaternionGroup 2, k * g * k⁻¹ = g⁻¹ → (f g)⁻¹ = f g := by
    intro g k h
    rw [← map_inv, ← h, map_mul, map_mul, map_inv, mul_comm (f k), mul_assoc, mul_inv_cancel,
      mul_one]
  have hx0 : (f (xa 0))⁻¹ = f (xa 0) := hinv (xa 0) (a 1) (by decide)
  have hx1 : (f (xa 1))⁻¹ = f (xa 1) := hinv (xa 1) (a 1) (by decide)
  have e0 : f (a 1) = f (xa 0) := by
    rcases hsame (a 1) (xa 0) (by decide) (by decide) (by decide) (by decide) with h | h
    · exact h
    · rw [h, hx0]
  have e1 : f (a 1) = f (xa 1) := by
    rcases hsame (a 1) (xa 1) (by decide) (by decide) (by decide) (by decide) with h | h
    · exact h
    · rw [h, hx1]
  have hxa : (xa 1 : QuaternionGroup 2) = xa 0 * a 1 := by decide
  have hone : f (a 1) = 1 := by
    have h := e1
    rw [hxa, map_mul, ← e0] at h
    exact mul_eq_left.mp h.symm
  have hx0one : f (xa 0) = 1 := by rw [← e0, hone]
  have ha : ∀ k : ZMod (2 * 2), (a k : QuaternionGroup 2) = (a 1) ^ k.val := fun k => by
    rw [a_one_pow, ZMod.natCast_zmod_val]
  cases y with
  | a k => rw [ha k, map_pow, hone, one_pow]
  | xa k =>
    have h : (xa k : QuaternionGroup 2) = xa 0 * a k := by rw [xa_mul_a, zero_add]
    rw [h, map_mul, hx0one, one_mul, ha k, map_pow, hone, one_pow]

end CFSG.ClassicalInvolution.Q3.TL4
