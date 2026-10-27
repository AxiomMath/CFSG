module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatRelativeFamily
public import CFSG.CharacterTheory.Wreathed.ConditionalGlobalDegreesValues

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.FlatRelative

open CFSG.Wreathed.ConditionalGeneralBase CFSG.Wreathed.FlatComplete
  CFSG.Wreathed.ConditionalGlobalDegrees

namespace Support

variable {ι : Type*} {BB : Finset ι} {m M : ℕ} {V : Finset (ZMod m × ZMod m)}
  {X : ZMod m → ι → ℂ} {c : ZMod m → ZMod m → ι → ℂ} {δ₀ δ₁ δ₂ δ₃ δ₄ α γ : ℤ}
  {χ₀ χ₁ χ₂ χ₃ χ₄ : ι} {ξ : ℕ → ι} {P Q : ℕ → Fin 2 → ι} {ψ : ZMod m × ZMod m → ι}
  {er : ℕ → Fin 2}
  (hS : Support BB m M V X c δ₀ δ₁ δ₂ δ₃ δ₄ α γ χ₀ χ₁ χ₂ χ₃ χ₄ ξ P Q ψ er)
include hS

theorem values [NeZero m] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) {k : ℕ} (hk : k ∈ Finset.Ico 1 m)
    (val : ι → ℂ) (lam Φ : ℂ) (ε : ℤ)
    (hsec : ∀ χ ∈ BB, 2 * val χ = lam * ((1 - ε * Φ) *
      ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) * X j χ + (1 + ε * Φ) *
        ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) *
          (∑ i : ZMod m, c i (0 - i) χ - ∑ i : ZMod m, c i (-(j : ZMod m) - i) χ))) :
    val χ₀ = lam * δ₀ * ε * Φ ∧ val χ₁ = -(lam * δ₁) ∧
      val χ₂ = -(lam * δ₂ * (1 + (-1) ^ k * (1 + ε * Φ))) ∧
      val χ₃ = lam * δ₃ * (-1 + (1 + (-1) ^ k) * (1 + ε * Φ)) ∧
      val χ₄ = lam * δ₄ * (1 + ε * Φ) ∧
      ∀ h ∈ (Finset.Ico 1 m).filter Odd,
        val (ξ h) = lam * α * (1 - ε * Φ) * ζ ^ (-((h : ℤ) * k)) := by
  have hval : ∀ χ ∈ BB, 2 * val χ = lam * (1 - ε * Φ) *
      ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) * X j χ + lam * (1 + ε * Φ) *
        ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) *
          (∑ i : ZMod m, c i (0 - i) χ - ∑ i : ZMod m, c i (-(j : ZMod m) - i) χ) :=
    fun χ hχ => by rw [hsec χ hχ]; ring
  have hX := hS.x_core
  have h₀ := value_off_zero (X := fun j => X (j : ZMod m) χ₀) (f := fun i j => c i j χ₀) hζ hk
    (fun j hj => (hX j hj).1) (by simpa using (hS.c_core (0, 0)).1)
    (fun i j hij => by rw [(hS.c_core (i, j)).1, ite_eq_right hij]) (hval χ₀ hS.memχ₀)
  have h₁ := value_off_zero (X := fun j => X (j : ZMod m) χ₁) (f := fun i j => c i j χ₁) hζ hk
    (fun j hj => (hX j hj).2.1) (by simpa using (hS.c_core (0, 0)).2.1)
    (fun i j hij => by rw [(hS.c_core (i, j)).2.1, ite_eq_right hij]) (hval χ₁ hS.memχ₁)
  have h₄ := value_off_zero (X := fun j => X (j : ZMod m) χ₄) (f := fun i j => c i j χ₄) hζ hk
    (fun j hj => (hX j hj).2.2.2.2) (by simpa using (hS.c_core (0, 0)).2.2)
    (fun i j hij => by rw [(hS.c_core (i, j)).2.2, ite_eq_right hij]) (hval χ₄ hS.memχ₄)
  have h₂ := value_middle (X := fun j => X (j : ZMod m) χ₂) (f := fun i j => c i j χ₂) hS.hm
    hS.hM hζ hk (fun j hj => (hX j hj).2.2.1) (fun i j => (hS.c_mid (i, j)).1)
    (hval χ₂ hS.memχ₂)
  have h₃ := value_middle (X := fun j => X (j : ZMod m) χ₃) (f := fun i j => c i j χ₃) hS.hm
    hS.hM hζ hk (fun j hj => (hX j hj).2.2.2.1) (fun i j => (hS.c_mid (i, j)).2)
    (hval χ₃ hS.memχ₃)
  refine ⟨by linear_combination h₀ / 2, by linear_combination h₁ / 2,
    by linear_combination h₂ / 2, by linear_combination h₃ / 2, by linear_combination h₄ / 2,
    fun h hh => ?_⟩
  have hξ := value_single (X := fun j => X (j : ZMod m) (ξ h)) (f := fun i j => c i j (ξ h))
    (A₂ := lam * (1 + ε * Φ)) (Finset.mem_filter.mp hh).1 (hS.x_odd hh)
    (fun i j => hS.c_odd hh (i, j)) (hval (ξ h) (hS.memξ h hh))
  linear_combination hξ / 2

theorem values_even [NeZero m] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) (hpow : ∃ n, m = 2 ^ n)
    (val : ι → ℂ) (lam Φ : ℂ) (ε : ℤ)
    (hsec : ∀ χ ∈ BB, 2 * val χ = lam * ((1 - ε * Φ) *
      ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * M)) * X j χ + (1 + ε * Φ) *
        ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * M)) *
          (∑ i : ZMod m, c i (0 - i) χ - ∑ i : ZMod m, c i (-(j : ZMod m) - i) χ)))
    {r : ℕ} (hr : r ∈ Finset.Ico 1 M) (e : Fin 2) :
    val (P r e) = -(lam * δ₂ * (1 + (-1) ^ r * (1 + ε * Φ))) ∧
      val (Q r e) = lam * δ₃ * (-1 + (1 + (-1) ^ r) * (1 + ε * Φ)) := by
  have hval : ∀ χ ∈ BB, 2 * val χ = lam * (1 - ε * Φ) *
      ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * M)) * X j χ + lam * (1 + ε * Φ) *
        ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * M)) *
          (∑ i : ZMod m, c i (0 - i) χ - ∑ i : ZMod m, c i (-(j : ZMod m) - i) χ) :=
    fun χ hχ => by rw [hsec χ hχ]; ring
  have hi₀ : (if e = er r then (r : ZMod m) else (r : ZMod m) + M) = (r : ZMod m) ∨
      (if e = er r then (r : ZMod m) else (r : ZMod m) + M) = ((r + M : ℕ) : ZMod m) := by
    by_cases he : e = er r
    · exact Or.inl (ite_eq_left he)
    · exact Or.inr (by rw [ite_eq_right he, Nat.cast_add])
  obtain ⟨hPB, hQB⟩ := hS.memPQ r hr e
  have hP := value_diag (X := fun j => X (j : ZMod m) (P r e)) (f := fun i j => c i j (P r e))
    hS.hm hS.hM hζ hpow hr hi₀ (fun j hj => (hS.x_even hr e j hj).1)
    (fun i j => (hS.c_even hr e (i, j)).1) (hval _ hPB)
  have hQ := value_diag (X := fun j => X (j : ZMod m) (Q r e)) (f := fun i j => c i j (Q r e))
    hS.hm hS.hM hζ hpow hr hi₀ (fun j hj => (hS.x_even hr e j hj).2)
    (fun i j => (hS.c_even hr e (i, j)).2) (hval _ hQB)
  exact ⟨by linear_combination hP / 2, by linear_combination hQ / 2⟩

end Support

end CFSG.Wreathed.FlatRelative
