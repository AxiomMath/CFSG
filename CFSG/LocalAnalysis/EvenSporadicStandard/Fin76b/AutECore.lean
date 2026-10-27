module

public import Mathlib.Algebra.Group.End

public section

namespace CFSG.EvenSporadicStandard.Fin76b

@[expose] def AutEFact (H : Type*) [Group H] : Prop :=
  ∀ b a : MulAut H, b ^ 3 = 1 → b ≠ 1 → a * b = b * a →
    (∃ d : H, b d = d ∧ ∀ e : H, b e = e → a e = d * e * d⁻¹) →
    ∃ d : H, b d = d ∧ ∃ j : ℕ, ∀ e : H, a e = d * (b ^ j) e * d⁻¹

theorem mulAut_congr_apply_apply {G H : Type*} [Group G] [Group H] (e : G ≃* H) (f : MulAut G)
    (x : G) : MulAut.congr e f (e x) = e (f x) := by
  simp [MulAut.congr_apply]

theorem AutEFact.of_mulEquiv {H H' : Type*} [Group H] [Group H'] (e : H ≃* H')
    (h : AutEFact H) : AutEFact H' := by
  intro b a hb3 hb1 hab hin
  obtain ⟨b0, rfl⟩ := (MulAut.congr e).surjective b
  obtain ⟨a0, rfl⟩ := (MulAut.congr e).surjective a
  have hb3' : b0 ^ 3 = 1 := (MulAut.congr e).injective (by rw [map_pow, map_one]; exact hb3)
  have hb1' : b0 ≠ 1 := fun h1 => hb1 (by rw [h1, map_one])
  have hab' : a0 * b0 = b0 * a0 :=
    (MulAut.congr e).injective (by rw [map_mul, map_mul]; exact hab)
  obtain ⟨d', hd', hin'⟩ := hin
  obtain ⟨d, hd, j, hj⟩ := h b0 a0 hb3' hb1' hab' ⟨e.symm d', by
      apply e.injective
      rw [← mulAut_congr_apply_apply, MulEquiv.apply_symm_apply]
      exact hd', fun x hx => by
      apply e.injective
      rw [← mulAut_congr_apply_apply, hin' (e x) (by rw [mulAut_congr_apply_apply, hx])]
      simp⟩
  refine ⟨e d, ?_, j, fun x => ?_⟩
  · rw [mulAut_congr_apply_apply, hd]
  · obtain ⟨y, rfl⟩ := e.surjective x
    rw [mulAut_congr_apply_apply, hj y, ← map_pow, mulAut_congr_apply_apply]
    simp

end CFSG.EvenSporadicStandard.Fin76b
