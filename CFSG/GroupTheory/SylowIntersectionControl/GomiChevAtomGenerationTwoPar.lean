module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevAtomGenerationSimple
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoPar
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoAssembly
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoMap

public section

namespace CFSG.GroupTheory

open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

theorem gomiAtomGenerationTop_of_twoPar {X : Type} [Group X] [Finite X] {T P₁ P₂ : Subgroup X}
    (h : TwoPar X T P₁ P₂) : GomiAtomGenerationTop X := by
  intro U Q hU hQ
  have hU' : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2 hU
  obtain ⟨P₁', P₂', h'⟩ := h.exists_of_equiv (MulEquiv.refl X) hU'
  have atom₁ : IsGomiAtom ⊤ U P₁' := by
    refine ⟨?_, le_top, ?_⟩
    · rw [top_inf_eq]; exact h'.lt₁
    · intro R hR1 hR2
      rw [top_inf_eq] at hR1
      rcases h'.atom₁ R hR1.le hR2 with e | e
      · exact absurd e hR1.ne'
      · exact e
  have atom₂ : IsGomiAtom ⊤ U P₂' := by
    refine ⟨?_, le_top, ?_⟩
    · rw [top_inf_eq]; exact h'.lt₂
    · intro R hR1 hR2
      rw [top_inf_eq] at hR1
      rcases h'.atom₂ R hR1.le hR2 with e | e
      · exact absurd e hR1.ne'
      · exact e
  rcases h'.hover Q hQ with rfl | rfl | rfl | rfl
  · exact le_sup_left
  · refine le_sup_of_le_right ?_
    exact le_sSup ⟨atom₁, le_rfl⟩
  · refine le_sup_of_le_right ?_
    exact le_sSup ⟨atom₂, le_rfl⟩
  · nth_rewrite 1 [← h'.sup_eq_top]
    refine sup_le ?_ ?_
    · refine le_sup_of_le_right ?_
      exact le_sSup ⟨atom₁, le_top⟩
    · refine le_sup_of_le_right ?_
      exact le_sSup ⟨atom₂, le_top⟩

end CFSG.GroupTheory
