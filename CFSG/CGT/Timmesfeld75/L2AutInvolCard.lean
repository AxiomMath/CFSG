module

public import CFSG.CGT.Timmesfeld75.L2AutInvol

public section

namespace CFSG.CGT.Timmesfeld75

open scoped MatrixGroups
open CFSG.Open

theorem IsL2Pair.autInvol_inner_or_field_card {Q : Type} [Group Q] {S : Subgroup Q} {q : ℕ}
    (hQ : IsL2Pair Q S q) (φ : Q ≃* Q) (hφ : ∀ x, φ (φ x) = x) :
    (∃ g : Q, g * g = 1 ∧ ∀ x, φ x = g * x * g⁻¹) ∨
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (e : Q ≃* SL(2, F)) (σ : F ≃+* F),
      Nat.card F = q ∧ σ ≠ RingEquiv.refl F ∧
        ∀ x, e (φ x) = Matrix.SpecialLinearGroup.map (σ : F →+* F) (e x) := by
  obtain ⟨F, i1, i2, i3, e0, hcard, -⟩ := hQ
  obtain ⟨ψ, hψ⟩ : ∃ ψ : SL(2, F) ≃* SL(2, F), ∀ y, ψ y = e0 (φ (e0.symm y)) :=
    ⟨e0.symm.trans (φ.trans e0), fun y => rfl⟩
  have hψψ : ∀ y, ψ (ψ y) = y := fun y => by
    rw [hψ, hψ, e0.symm_apply_apply, hφ, e0.apply_symm_apply]
  rcases CFSG.CGT.Timmesfeld75.autInvol_inner_or_field ψ hψψ with
    ⟨g, hgg, hg⟩ | ⟨k, σ, hσ, hk⟩
  · left
    refine ⟨e0.symm g, e0.injective ?_, fun x => e0.injective ?_⟩
    · rw [map_mul, e0.apply_symm_apply, hgg, map_one]
    · have h1 := hg (e0 x)
      rw [hψ, e0.symm_apply_apply] at h1
      rw [h1, map_mul, map_mul, map_inv, e0.apply_symm_apply]
  · right
    refine ⟨F, i1, i2, i3, e0.trans (MulAut.conj k), σ, hcard, hσ, fun x => ?_⟩
    have h1 := hk (e0 x)
    rw [hψ, e0.symm_apply_apply] at h1
    show k * e0 (φ x) * k⁻¹ = Matrix.SpecialLinearGroup.map (σ : F →+* F) (k * e0 x * k⁻¹)
    exact h1

end CFSG.CGT.Timmesfeld75
