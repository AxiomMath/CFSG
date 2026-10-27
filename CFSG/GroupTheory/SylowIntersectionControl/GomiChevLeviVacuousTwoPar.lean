module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviVacuous
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoPar
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoMap

public section

namespace CFSG.GroupTheory

open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

theorem gomiAtomsOnlyTop_of_twoPar {X : Type} [Group X] [Finite X] {T P₁ P₂ : Subgroup X}
    (h : TwoPar X T P₁ P₂) : GomiAtomsOnlyTop X := by
  intro U Q hU hBQ hQ
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
  rcases h'.hover Q hBQ.le with rfl | rfl | rfl | rfl
  · exact absurd rfl hBQ.ne
  · exact atom₁
  · exact atom₂
  · exact absurd rfl hQ.ne

end CFSG.GroupTheory
