module

public import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Tactic.Group

public section

namespace CFSG.ClassicalInvolution.Sp62Rec.I1

theorem exists_hom_of_index_two {Γ H : Type*} [Group Γ] [Group H] (N : Subgroup Γ) [N.Normal]
    (τ : Γ) (hτ2 : τ * τ = 1) (hτN : τ ∉ N) (hΓ : ∀ g : Γ, g ∈ N ∨ g * τ⁻¹ ∈ N)
    (f : N →* H) (w : H) (hw2 : w * w = 1)
    (hf : ∀ (x : Γ) (hx : x ∈ N),
      f ⟨τ * x * τ⁻¹, ‹N.Normal›.conj_mem x hx τ⟩ = w * f ⟨x, hx⟩ * w⁻¹) :
    ∃ F : Γ →* H, (∀ (x : Γ) (hx : x ∈ N), F x = f ⟨x, hx⟩) ∧ F τ = w ∧
      ∀ (g : Γ), g ∉ N → ∃ (x : Γ) (hx : x ∈ N), F g = f ⟨x, hx⟩ * w := by
  classical
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
  let G0 : Γ → H := fun g =>
    if hg : g ∈ N then f ⟨g, hg⟩
    else if hg' : g * τ⁻¹ ∈ N then f ⟨g * τ⁻¹, hg'⟩ * w else 1
  have hG0N : ∀ (g : Γ) (hg : g ∈ N), G0 g = f ⟨g, hg⟩ := by
    intro g hg; simp [G0, hg]
  have hG0τ : ∀ (g : Γ) (hg : g ∉ N) (hg' : g * τ⁻¹ ∈ N), G0 g = f ⟨g * τ⁻¹, hg'⟩ * w := by
    intro g hg hg'; simp [G0, hg, hg']
  have hnot : ∀ g : Γ, g ∉ N → g * τ⁻¹ ∈ N := fun g hg => (hΓ g).resolve_left hg
  refine ⟨{ toFun := G0, map_one' := ?_, map_mul' := ?_ }, ?_, ?_, ?_⟩
  · rw [hG0N 1 N.one_mem]; exact map_one f
  · intro g g'
    by_cases hg : g ∈ N <;> by_cases hg' : g' ∈ N
    ·
      have hgg : g * g' ∈ N := N.mul_mem hg hg'
      rw [hG0N _ hgg, hG0N _ hg, hG0N _ hg']
      exact map_mul f ⟨g, hg⟩ ⟨g', hg'⟩
    ·
      have hgg : g * g' ∉ N := fun h => hg' (by simpa using N.mul_mem (N.inv_mem hg) h)
      have h1 := hnot g' hg'
      have h2 : g * g' * τ⁻¹ ∈ N := by simpa [mul_assoc] using N.mul_mem hg h1
      rw [hG0τ _ hgg h2, hG0N _ hg, hG0τ _ hg' h1]
      have : (⟨g * g' * τ⁻¹, h2⟩ : N) = ⟨g, hg⟩ * ⟨g' * τ⁻¹, h1⟩ :=
        Subtype.ext (by simp [mul_assoc])
      rw [this, map_mul, mul_assoc]
    ·
      have hgg : g * g' ∉ N := fun h => hg (by simpa using N.mul_mem h (N.inv_mem hg'))
      have h1 := hnot g hg
      have h2 : g * g' * τ⁻¹ ∈ N := by
        have : g * g' * τ⁻¹ = (g * τ⁻¹) * (τ * g' * τ⁻¹) := by group
        rw [this]; exact N.mul_mem h1 (‹N.Normal›.conj_mem g' hg' τ)
      rw [hG0τ _ hgg h2, hG0τ _ hg h1, hG0N _ hg']
      have : (⟨g * g' * τ⁻¹, h2⟩ : N) =
          ⟨g * τ⁻¹, h1⟩ * ⟨τ * g' * τ⁻¹, ‹N.Normal›.conj_mem g' hg' τ⟩ :=
        Subtype.ext (by simp only [Subgroup.coe_mul]; group)
      rw [this, map_mul, hf g' hg']
      calc f ⟨g * τ⁻¹, h1⟩ * (w * f ⟨g', hg'⟩ * w⁻¹) * w
          = f ⟨g * τ⁻¹, h1⟩ * w * f ⟨g', hg'⟩ * (w⁻¹ * w) := by group
        _ = f ⟨g * τ⁻¹, h1⟩ * w * f ⟨g', hg'⟩ := by simp
    ·
      have hgg : g * g' ∈ N := by
        have h1 := hnot g hg
        have h2 := hnot g' hg'
        have : g * g' = (g * τ⁻¹) * (τ * (g' * τ⁻¹) * τ⁻¹) * (τ * τ) := by group
        rw [this, hτ2, mul_one]
        exact N.mul_mem h1 (‹N.Normal›.conj_mem _ h2 τ)
      have h1 := hnot g hg
      have h2 := hnot g' hg'
      rw [hG0N _ hgg, hG0τ _ hg h1, hG0τ _ hg' h2]
      have : (⟨g * g', hgg⟩ : N) =
          ⟨g * τ⁻¹, h1⟩ * ⟨τ * (g' * τ⁻¹) * τ⁻¹, ‹N.Normal›.conj_mem _ h2 τ⟩ :=
        Subtype.ext (by
          simp only [Subgroup.coe_mul]
          have : g * g' = (g * τ⁻¹) * (τ * (g' * τ⁻¹) * τ⁻¹) * (τ * τ) := by group
          rw [this, hτ2, mul_one])
      rw [this, map_mul, hf _ h2]
      calc f ⟨g * τ⁻¹, h1⟩ * (w * f ⟨g' * τ⁻¹, h2⟩ * w⁻¹)
          = f ⟨g * τ⁻¹, h1⟩ * w * f ⟨g' * τ⁻¹, h2⟩ * w⁻¹ := by group
        _ = f ⟨g * τ⁻¹, h1⟩ * w * (f ⟨g' * τ⁻¹, h2⟩ * w) := by rw [hwinv]; group
  · intro x hx; exact hG0N x hx
  · have h1 : τ * τ⁻¹ ∈ N := by simp
    show G0 τ = w
    rw [hG0τ τ hτN (by simp)]
    have : (⟨τ * τ⁻¹, by simp⟩ : N) = 1 := Subtype.ext (by simp)
    rw [this, map_one, one_mul]
  · intro g hg
    have h1 := hnot g hg
    refine ⟨g * τ⁻¹, h1, ?_⟩
    exact hG0τ g hg h1

end CFSG.ClassicalInvolution.Sp62Rec.I1
