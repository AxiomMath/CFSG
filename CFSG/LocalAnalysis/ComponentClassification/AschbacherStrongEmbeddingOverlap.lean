module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type*} [Group G]

@[expose] def overlapClosure (A₁ A₂ : Subgroup G) : Subgroup G :=
  Subgroup.closure {g : G | ∃ X ∈ ({A₁, A₂} : Set (Subgroup G)),
    ∃ Y ∈ ({A₁, A₂} : Set (Subgroup G)), rightConjugate X g ⊓ Y ≠ ⊥}

theorem mem_overlapClosure {A₁ A₂ X Y : Subgroup G} (hX : X = A₁ ∨ X = A₂)
    (hY : Y = A₁ ∨ Y = A₂) {g : G} (hg : rightConjugate X g ⊓ Y ≠ ⊥) :
    g ∈ overlapClosure A₁ A₂ :=
  Subgroup.subset_closure ⟨X, by rcases hX with rfl | rfl <;> simp, Y,
    by rcases hY with rfl | rfl <;> simp, hg⟩

theorem mem_overlapClosure_of_conj {A₁ A₂ X Y : Subgroup G} (hX : X = A₁ ∨ X = A₂)
    (hY : Y = A₁ ∨ Y = A₂) {a g : G} (ha : a ∈ X) (ha1 : a ≠ 1) (hag : g⁻¹ * a * g ∈ Y) :
    g ∈ overlapClosure A₁ A₂ := by
  refine mem_overlapClosure hX hY fun hbot => ?_
  have hconj : g⁻¹ * a * g ∈ rightConjugate X g := by
    rw [mem_rightConjugate_iff]
    simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using ha
  have hmem : g⁻¹ * a * g ∈ rightConjugate X g ⊓ Y := ⟨hconj, hag⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  apply ha1
  calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    _ = 1 := by rw [hmem, mul_one, mul_inv_cancel]

end CFSG.ComponentClassification.AschbacherStrongEmbedding
