module

public import CFSG.LocalAnalysis.OddStandard.ThmCSylowQ8
public import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices

public section

namespace CFSG.OddStandard.ThmC.Sylow

open CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices CFSG.OddStandard.ThmC.T

theorem not_isT_of_commuting_sl2 {K : Type} [Group K] [Finite K] (T : Sylow 2 K)
    (hT : IsT (T : Subgroup K)) {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
    (h₁ : ringChar F₁ ≠ 2) (h₂ : ringChar F₂ ≠ 2)
    (φ₁ : Matrix.SpecialLinearGroup (Fin 2) F₁ →* K)
    (φ₂ : Matrix.SpecialLinearGroup (Fin 2) F₂ →* K)
    (i₁ : Function.Injective φ₁) (i₂ : Function.Injective φ₂)
    (hc : ∀ A B, Commute (φ₁ A) (φ₂ B)) : False := by
  obtain ⟨a₁, b₁, e₁⟩ := (odd_field_two_dimensional_quaternion_matrices h₁).1
  obtain ⟨a₂, b₂, e₂⟩ := (odd_field_two_dimensional_quaternion_matrices h₂).1
  exact not_isT_of_q8_pair T hT (φ₁.comp (quatHom e₁)) (φ₂.comp (quatHom e₂))
    (fun a b => hc _ _) (i₁.comp (quatHom_injective h₁ e₁)) (i₂.comp (quatHom_injective h₂ e₂))

end CFSG.OddStandard.ThmC.Sylow
