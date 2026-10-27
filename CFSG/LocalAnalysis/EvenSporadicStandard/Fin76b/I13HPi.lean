module

public import Mathlib.Algebra.Group.End

public section

namespace CFSG.EvenSporadicStandard.Fin76b

variable {H : Type*} [Group H]

theorem exists_perm_hom_of_pairs (s : H) (r : Fin 5 → H) (hs : ∀ φ : MulAut H, φ s = s)
    (hs2 : s * s = 1) (hr : ∀ i, r i * r i = 1 ∧ r i ≠ 1 ∧ r i ≠ s)
    (hb : ∀ x : H, x * x = 1 → x ≠ 1 → x ≠ s → ∃! i : Fin 5, x = r i ∨ x = r i * s) :
    ∃ π : MulAut H →* Equiv.Perm (Fin 5), ∀ (φ : MulAut H) (i j : Fin 5),
      π φ i = j ↔ (φ (r i) = r j ∨ φ (r i) = r j * s) := by
  have hP : ∀ (φ : MulAut H) (i : Fin 5),
      φ (r i) * φ (r i) = 1 ∧ φ (r i) ≠ 1 ∧ φ (r i) ≠ s := by
    intro φ i
    obtain ⟨h1, h2, h3⟩ := hr i
    exact ⟨by rw [← map_mul, h1, map_one],
      fun h => h2 (φ.injective (h.trans (map_one φ).symm)),
      fun h => h3 (φ.injective (h.trans (hs φ).symm))⟩
  choose g hg using fun (φ : MulAut H) (i : Fin 5) =>
    hb (φ (r i)) (hP φ i).1 (hP φ i).2.1 (hP φ i).2.2
  have g_spec : ∀ φ i j, g φ i = j ↔ (φ (r i) = r j ∨ φ (r i) = r j * s) := by
    intro φ i j
    exact ⟨fun h => h ▸ (hg φ i).1, fun h => ((hg φ i).2 j h).symm⟩
  have g_mul : ∀ φ ψ i, g (φ * ψ) i = g φ (g ψ i) := by
    intro φ ψ i
    rw [g_spec]
    have h1 := (g_spec ψ i (g ψ i)).1 rfl
    have h2 := (g_spec φ (g ψ i) (g φ (g ψ i))).1 rfl
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact Or.inl (by rw [MulAut.mul_apply, h1, h2])
    · exact Or.inr (by rw [MulAut.mul_apply, h1, h2])
    · exact Or.inr (by rw [MulAut.mul_apply, h1, map_mul, hs, h2])
    · exact Or.inl (by rw [MulAut.mul_apply, h1, map_mul, hs, h2, mul_assoc, hs2, mul_one])
  have g_one : ∀ i, g 1 i = i := fun i => (g_spec 1 i i).2 (Or.inl rfl)
  refine ⟨MonoidHom.mk' (fun φ => ⟨g φ, g φ⁻¹, fun i => ?_, fun i => ?_⟩)
    fun φ ψ => Equiv.ext fun i => g_mul φ ψ i, fun φ i j => g_spec φ i j⟩
  · rw [← g_mul, inv_mul_cancel, g_one]
  · rw [← g_mul, mul_inv_cancel, g_one]

end CFSG.EvenSporadicStandard.Fin76b
