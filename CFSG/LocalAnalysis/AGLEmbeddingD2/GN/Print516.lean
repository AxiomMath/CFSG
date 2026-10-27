module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Final
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.AltSevenA1
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenCentreFinal
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8Smith
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Final
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Chev

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def AGL81I516 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ C₁ C₂ : Subgroup X, IsC118Pair T C₁ C₂ → GNParabolic T C₁ C₂

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem glaubermanNiles_of_print (h516 : AGL81I516) (hG : KFactChevGenThree)
    (hGC : KFactChevGenCentre)
    (hFF : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem) (hAlt : GNAltFacts) :
    GlaubermanNilesInput := by
  refine glaubermanNiles_of_yFacts fun X _ _ T hX hT C₁ C₂ hP => ?_
  have hpar : GNParabolic T C₁ C₂ := h516 X T hX C₁ C₂ hP
  have hcov : ∀ {L : Subgroup (X ⧸ gnC T)}, GNYComponent T C₁ C₂ L →
      IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → ParabolicCover T C₁ C₂ L :=
    fun hY hcl P hPb => hpar _ hY.1 (isChevTwo_of_classicalTwoOrG2 hcl) P hPb
  refine ⟨fun L hY => ⟨fun hChev P hPL => hpar L hY.1 hChev P hPL, fun hLT ⟨e⟩ => ?_,
    fun n hn ⟨e⟩ => ?_⟩, fun L hY => ?_, fun L hY hLT p hp hpZ => ?_⟩
  · obtain ⟨-, he⟩ := center_eq_bot_and_quotient_of_mulEquiv_alternatingGroup (by norm_num) e
    exact (hAlt X T hX hT C₁ C₂ hP L hY 7 (Or.inl rfl) he).2.2 (Or.inr hLT)
  · obtain ⟨-, he⟩ := center_eq_bot_and_quotient_of_mulEquiv_alternatingGroup (by omega) e
    exact (hAlt X T hX hT C₁ C₂ hP L hY n (Or.inr hn) he).2.2 (Or.inl hn)
  · rcases classical_or_alt_of_gnYComponent hFF hX hP hY with hcl | ⟨n, hn, he⟩
    · obtain ⟨h1, h2⟩ := (gnThree_gnCentre_of_cover hG hGC hX hP hY hcl (hcov hY hcl)).1
      exact ⟨h1, fun _ => h2⟩
    · refine ⟨(hAlt X T hX hT C₁ C₂ hP L hY n hn he).2.1, fun hc => ?_⟩
      rcases hc with hcl | ⟨-, hna⟩
      · exact (gnThree_gnCentre_of_cover hG hGC hX hP hY hcl (hcov hY hcl)).1.2
      · exact absurd ⟨n, by omega, he⟩ hna
  · rcases classical_or_alt_of_gnYComponent hFF hX hP hY with hcl | ⟨n, hn, he⟩
    · exact (gnThree_gnCentre_of_cover hG hGC hX hP hY hcl (hcov hY hcl)).2 hLT p hp hpZ
    · have hZ := (hAlt X T hX hT C₁ C₂ hP L hY n hn he).1
      rw [hZ, Subgroup.card_bot] at hpZ
      exact absurd (Nat.le_of_dvd one_pos hpZ) (not_le.mpr hp.one_lt)

theorem glaubermanNiles_of_print_gf2 (h516 : AGL81I516) (hG : KFactChevGenThree)
    (hGC : KFactChevGenCentre)
    (hFF : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem)
    (hGF : CFSG.HardMathSupport.Cooperstein.Coordinator.GF2EightFive) (hR : GNAltRest) :
    GlaubermanNilesInput :=
  glaubermanNiles_of_print h516 hG hGC hFF (gnAltFacts_of_gf2EightFive hGF hR)

section Cited

set_option linter.unusedSectionVars false


theorem glaubermanNiles_of_print_cited (h516 : AGL81I516)
    (hFF : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem)
    (hR : GNAltSevenThreeRank) : GlaubermanNilesInput :=
  glaubermanNiles_of_print_gf2 h516 Tits.MsideParabolicEscape.ChevGen.kFactChevGenThree_proved
    Tits.MsideParabolicEscape.ChevGen.kFactChevGenCentre_proved hFF
    (CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.gf2EightFive_of_b42L42Core
      CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.b42L42Core_holds)
    (gnAltRest_of_seven (gnAltRestSeven_of_threeRank hR))

end Cited

end CFSG.AGLEmbeddingD2.GN
