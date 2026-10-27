module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalViso

public section

namespace CFSG.HardMathSupport.Foote.E27

open Subgroup CFSG.AGLEmbedding CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.GH74.Exceptional
  CFSG.Fischer.Classification

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem U2_four_mulEquiv_catGroup_u42 : Nonempty (Unitary.U2 4 ≃* CatGroup u42Index) := by
  have h : CFSG.Open.StatedClassicalModel (CatGroup u42Index) .PSU 4 2 1 := by
    rcases lieModel_u42 with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact h
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have : Fintype CFSG.Blueprint.Fischer.K := Fintype.ofFinite _
  have hc : Fintype.card K = Fintype.card CFSG.Blueprint.Fischer.K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, Unitary.card_K]
  let e₁ := CFSG.Fischer.Classification.Recognition.statedProjSUEquiv
    (FiniteField.ringEquivOfCardEq hc) 4 (2 ^ 1)
  exact ⟨u2FourEquiv.trans (e.trans e₁).symm⟩

end CFSG.HardMathSupport.Foote.E27

end
