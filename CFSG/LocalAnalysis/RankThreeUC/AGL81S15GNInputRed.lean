module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FFGlaubermanNiles
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15C118Sub

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN CFSG.Quasithin
  CFSG.AGLEmbedding

@[expose] def S15GNFactorShape : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T → T ≠ ⊥ →
    ∀ T₁ T₂ : Subgroup X, IsC118Pair T T₁ T₂ →
      (GNFactor T T₁ T₂ ∧ (GNCoverP T T₁ T₂ ∧ GNCoverSec T T₁ T₂)) ∧ GNShape T T₁ T₂

namespace GNInputRed

theorem gnYFacts_of_print (h516 : AGL81I516) (hG : KFactChevGenThree) (hGC : KFactChevGenCentre)
    (hFF : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem) (hAlt : GNAltFacts)
    {X : Type} [Group X] [Finite X] {T : Subgroup X} (hX : GNSetting X T) (hT : T ≠ ⊥)
    {C₁ C₂ : Subgroup X} (hP : IsC118Pair T C₁ C₂) :
    GNYComponentFacts T C₁ C₂ ∧ GNThree T C₁ C₂ ∧ GNCentre T C₁ C₂ := by
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

@[expose] def Factor : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T → T ≠ ⊥ →
    ∀ T₁ T₂ : Subgroup X, IsC118Pair T T₁ T₂ →
      GNFactor T T₁ T₂ ∧ (GNCoverP T T₁ T₂ ∧ GNCoverSec T T₁ T₂)

@[expose] def RankTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T → T ≠ ⊥ →
    ∀ T₁ T₂ : Subgroup X, IsC118Pair T T₁ T₂ → ∀ Ls : Subgroup (X ⧸ gnC T),
      GNYComponent T T₁ T₂ Ls → IsClassicalTwoOrG2 (↥Ls ⧸ Subgroup.center ↥Ls) →
        ¬ RankOneChevTwo (↥Ls ⧸ Subgroup.center ↥Ls)

@[expose] def AltEven : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T → T ≠ ⊥ →
    ∀ T₁ T₂ : Subgroup X, IsC118Pair T T₁ T₂ → ∀ Ls : Subgroup (X ⧸ gnC T),
      GNYComponent T T₁ T₂ Ls → ∀ n : ℕ, 8 < n →
        Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* alternatingGroup (Fin n)) → Even n

theorem gnShape_of_residuals (hFF : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem)
    (hAlt : GNAltFacts) (h1 : RankTwo) (h2 : AltEven) {X : Type} [Group X] [Finite X]
    {T : Subgroup X} (hX : GNSetting X T) (hT : T ≠ ⊥) {T₁ T₂ : Subgroup X}
    (hC : IsC118Pair T T₁ T₂) : GNShape T T₁ T₂ := by
  intro Ls hY
  obtain ⟨-, h1Z, -, -, h2B, h2c, -⟩ := id hC
  refine ⟨commutator_eq_of_gnYComponent hX h1Z h2B h2c hY, ?_⟩
  rcases classical_or_alt_of_gnYComponent hFF hX hC hY with hcl | ⟨n, hn, he⟩
  · exact Or.inl ⟨hcl, h1 X T hX hT T₁ T₂ hC Ls hY hcl⟩
  · have hZ := (hAlt X T hX hT T₁ T₂ hC Ls hY n hn he).1
    refine Or.inr ⟨n, hn.imp id fun h => ⟨h, h2 X T hX hT T₁ T₂ hC Ls hY n h he⟩, ⟨?_⟩⟩
    exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
      he.some

end GNInputRed

section Certified

namespace GNInputRed

theorem gnSix_of_isC118Pair
    {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hX : GNSetting X T) (hT : T ≠ ⊥) {C₁ C₂ : Subgroup X} (hP : IsC118Pair T C₁ C₂) :
    IsGNPair T C₁ C₂ ∧ GNParabolic T C₁ C₂ ∧ GNThree T C₁ C₂ ∧ GNCentre T C₁ C₂ ∧
      GNAlt7 T C₁ C₂ ∧ GNAltBig T C₁ C₂ := by
  obtain ⟨hF, h3, hc⟩ := gnYFacts_of_print
    (CFSG.AGLEmbeddingD2.Tits.GN516.agl81I516_of_graphOrbit
      CFSG.AGLEmbeddingD2.Tits.GN516.kFactChevGraphOrbit_proved
      CFSG.AGLEmbeddingD2.Tits.GN516.agl81I516SymOver_holds)
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen.kFactChevGenThree_proved
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen.kFactChevGenCentre_proved
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.ffModuleTheorem_holds
    (gnAltFacts_of_gf2EightFive
      (CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.gf2EightFive_of_b42L42Core
        CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.b42L42Core_holds)
      (gnAltRest_of_seven (gnAltRestSeven_of_threeRank
        CFSG.AGLEmbeddingD2.McLaughlin.A7Six.gnAltSevenThreeRank_proved))) hX hT hP
  obtain ⟨hP', h7, hB⟩ := gnParabolic_gnAlt7_gnAltBig_of_yFacts hF
  exact ⟨isGNPair_of_isC118Pair hP, hP', h3, hc, h7, hB⟩

theorem gnGood_of_isC118Pair
    (h : S15GNFactorShape) {X : Type} [Group X] [Finite X]
    {T : Subgroup X} (hX : GNSetting X T) (hT : T ≠ ⊥) {T₁ T₂ : Subgroup X}
    (hC : IsC118Pair T T₁ T₂) : GNGood T T₁ T₂ := by
  obtain ⟨hpair, hP, h3, hc, h7, hB⟩ := gnSix_of_isC118Pair hX hT hC
  obtain ⟨⟨hF, hCov⟩, hS⟩ := h X T hX hT T₁ T₂ hC
  refine ⟨hpair, hP, h3, hc, h7, hB, hF, hS, hC, fun X₁ hTX hX₁ _ => ?_, hCov⟩
  have hne : T.subgroupOf X₁ ≠ ⊥ := fun hbot =>
    hT ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hTX)
  exact (h ↥X₁ (T.subgroupOf X₁) hX₁ hne _ _ (hC.subgroupOf hTX)).1.1

theorem factorShape_of_residuals
    (hF : Factor) (h1 : RankTwo) (h2 : AltEven) :
    S15GNFactorShape := by
  intro X _ _ T hX hT T₁ T₂ hC
  exact ⟨hF X T hX hT T₁ T₂ hC, gnShape_of_residuals
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.ffModuleTheorem_holds
    (gnAltFacts_of_gf2EightFive
      (CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.gf2EightFive_of_b42L42Core
        CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.b42L42Core_holds)
      (gnAltRest_of_seven (gnAltRestSeven_of_threeRank
        CFSG.AGLEmbeddingD2.McLaughlin.A7Six.gnAltSevenThreeRank_proved))) h1 h2 hX hT hC⟩

end GNInputRed

theorem S15GNInput_of_factorShape
    (h : S15GNFactorShape) : S15GNInput := by
  intro X _ _ T hX hT
  obtain ⟨C₁, C₂, hC⟩ := exists_isC118Pair hX hT
  exact ⟨C₁, C₂, GNInputRed.gnGood_of_isC118Pair h hX hT hC⟩

end Certified

end CFSG.LocalAnalysis.RankThreeUC.S15
