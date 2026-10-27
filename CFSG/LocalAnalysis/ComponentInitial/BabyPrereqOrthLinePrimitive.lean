module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionProjective

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem orthogonal_singular_line_primitive [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    MulAction.IsPretransitive (elementaryGroup Q) (Points Q) ∧
      MulAction.IsPreprimitive (elementaryGroup Q) (Points Q) := by
  obtain ⟨T, hT3, hTs⟩ := hT
  obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ := exists_three_hypPairs hQ hT3.ge hTs
  have h := elementary_preprimitive_of_hypPairs Q hQ h₁₂ h₁₃ h₂₃
  exact ⟨h.toIsPretransitive, h⟩

end CFSG.LocalAnalysis.ComponentInitial
