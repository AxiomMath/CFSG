module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelAut
public import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelRadicals

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_le_sq_of_mul_self {F : Subgroup (projectiveSL 3 K)} (hF2 : ∀ a ∈ F, a * a = 1) :
    Nat.card F ≤ Nat.card K ^ 2 := by
  have hF2' : ∀ a ∈ F, a ^ 2 = 1 := fun a ha => by rw [sq]; exact hF2 a ha
  obtain ⟨g, hg⟩ := exists_conj_le_projUnip hF2'
  set F' := F.map (MulAut.conj g⁻¹).toMonoidHom with hF'
  have hcard : Nat.card F' = Nat.card F :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hF'U : F' ≤ projUnip K := by
    rintro _ ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply] using hg a ha
  have hF'2 : ∀ a ∈ F', a ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hF2' a ha, map_one]
  rw [← hcard]
  rcases le_projRad_of_le_projUnip hF'U hF'2 with h | h
  · exact (Subgroup.card_le_of_le h).trans (by rw [radicals_projUnip.card₁])
  · exact (Subgroup.card_le_of_le h).trans (by rw [radicals_projUnip.card₂])

end CFSG.LocalAnalysis.EvenBN.LinearThree
