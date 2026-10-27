module

public import CFSG.LargeExtraspecial.DWFldSymplectic
public import CFSG.LargeExtraspecial.DWFldOrth
public import CFSG.LargeExtraspecial.DWInsMain

public section

namespace CFSG.LargeExtraspecial.DW

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def DW2RootSL2Input : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (f : ℕ), 2 ≤ f →
    t ∈ ({.G2, .trialityD4, .F4, .E6, .twistedE6, .E7, .E8} : Finset StatedLieTag) →
    LieModel X t 0 2 f → ∀ D : Set X, IsTransClass34 D →
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ f ∧
        ∃ φ : Matrix.SpecialLinearGroup (Fin 2) F →* X, Function.Injective φ ∧
          ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, φ g ∈ D

theorem dw2FieldInput_of (h : DW2RootSL2Input) : DW2FieldInput := by
  intro X _ _ t n f hf ht hX D hD
  rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl | rfl, -⟩ | ⟨rfl, hexc⟩
  · exact false_of_lieModel_PSL hf hX hD
  · exact false_of_lieModel_PSp hf hX hD
  · exact false_of_lieModel_POmegaPlus hf hX hD
  · exact false_of_lieModel_POmegaMinus hf hX hD
  · obtain ⟨F, _, _, hF, φ, hφ, g, hg⟩ := h X t f hf hexc hX D hD
    have := charP_two_of_card_eq hF
    obtain ⟨s, hs0, hs1⟩ := exists_ne_zero_ne_one_of_card hF hf
    exact not_isTransClass34_of_sl2 hD hs0 hs1 φ hφ hg

end CFSG.LargeExtraspecial.DW
