module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecOverEleven
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarSecSeven
public import CFSG.LocalAnalysis.OddStandard.AltStdSecHBPartsTwo

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput LieOrderFormulasInput
  EvenLieOuterTwoComponentsInput)

@[expose] def ShapeTwoSmallTen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ) (z u : G),
    Setting G L n → Cyc L Q z → ShapeTwo L Q z u → n ≤ 10 → False

section Main


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {Q : Subgroup G} {z u : G}

theorem shapeTwo_dichotomy_eleven (htri : ExactShapeTrichotomy)
    (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    (hEO : EvenLieOuterTwoComponentsInput) (hR2 : RankTwoAlternatingStandard)
    (h : Setting G L 11) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin 11)) :
    CaseII e h.hn (L ⊔ zpowers u) z ∨ CaseII e h.hn (L ⊔ zpowers (u * z)) z ∨
      ∃ H : Subgroup G, WreathPair L z 11 H := by
  classical
  have h47 : ShapeTwoCentDoubleAt 11 := shapeTwoCentDoubleAt_eleven hGLS hO hEO hR2
  obtain ⟨S₀, S₁, hS₀, hS₁, hS01⟩ : ∃ S₀ S₁ : Finset (Fin 11),
      S₀.card = 3 ∧ S₁.card = 4 ∧ S₀ ⊆ S₁ :=
    ⟨{0, 1, 2}, {0, 1, 2, 3}, by decide, by decide, by decide⟩
  have hex : ExactShape z L 11 := exactShape_of_setting h d T.card
  have hK := isKGroupCat_of_kProper h.std.kProper
  have ht₁ : z ∈ centralizer (corr (X := G) e (altSub S₁) : Set G) :=
    t_mem_centralizer_corr (X := G) e hex (altSub S₁)
  have hm7 : 11 - S₁.card = 7 := by omega
  have hsec₁ := exactShape_section_root hex e (by omega) (by omega) ht₁
  rw [hm7] at hsec₁
  have hKcat₁ : CFSG.SectionRank.IsKGroupCat (Sec G (corr (X := G) e (altSub S₁))) :=
    isKGroupCat_sec hK
      (centralizer_ne_top_of_ne_one h (exists_ne_one_of_card_ge_three e (by omega)))
  have hO₁ := oddCore_sec_eq_bot (corr (X := G) e (altSub S₁))
  rcases exactShape_trichotomy_seven hGLS hO hEO hKcat₁ hO₁ hsec₁ with h1 | hW₁ | h1
  · exact (false_of_caseI htri h d T e (by norm_num) (by norm_num) (Or.inr hS₁) (by omega)
      ⟨ht₁, h1⟩).elim
  ·
    have ht₀ : z ∈ centralizer (corr (X := G) e (altSub S₀) : Set G) :=
      t_mem_centralizer_corr (X := G) e hex (altSub S₀)
    have hm8 : 11 - S₀.card = 8 := by omega
    have hsec₀ := exactShape_section_three hex e hS₀ (by omega) ht₀
    rw [hm8] at hsec₀
    have hKcat₀ : CFSG.SectionRank.IsKGroupCat (Sec G (corr (X := G) e (altSub S₀))) :=
      isKGroupCat_sec hK
        (centralizer_ne_top_of_ne_one h (exists_ne_one_of_card_ge_three e (by omega)))
    have hO₀ := oddCore_sec_eq_bot (corr (X := G) e (altSub S₀))
    have h49 : 49 ∣ Nat.card (Sec G (corr (X := G) e (altSub S₀))) := by
      have hdvd := (sq_card_dvd_of_wreath (by norm_num) hW₁).trans
        (card_sec_dvd_of_le (corr_mono e (altSub_mono hS01)))
      exact Nat.dvd_trans (by norm_num [Nat.factorial]) hdvd
    rcases central_or_wreath_eight hGLS hO hKcat₀ hO₀ hsec₀ h49 with h2 | h2
    · exact (false_of_caseI htri h d T e (by norm_num) (by norm_num) (Or.inl hS₀) (by omega)
        ⟨ht₀, h2⟩).elim
    · obtain ⟨H, hH⟩ := exists_wreathPair_of_caseIII_root hex e (by norm_num) hS₀
        ⟨ht₀, by rw [hm8]; exact h2⟩
      exact Or.inr (Or.inr ⟨H, hH⟩)
  · rcases caseII_of_centDoubleAt h47 h d T e (by norm_num) (Or.inr hS₁) (by omega)
      ⟨ht₁, by rw [hm7]; exact h1⟩ with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl h2)

theorem false_of_shapeTwo_eleven (htri : ExactShapeTrichotomy)
    (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    (hEO : EvenLieOuterTwoComponentsInput) (hR2 : RankTwoAlternatingStandard)
    (h : Setting G L 11) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin 11)) : False :=
  false_of_shapeTwo_of_dichotomy_of_unique (wreathPairUniqueAt_eleven hGLS hO) h d T.card
    (by norm_num) T.cent T.outer T.sq e (shapeTwo_dichotomy_eleven htri hGLS hO hEO hR2 h d T e)

theorem shapeTwoSmallEleven_of_ten (htri : ExactShapeTrichotomy)
    (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    (hEO : EvenLieOuterTwoComponentsInput) (hR2 : RankTwoAlternatingStandard)
    (h10 : ShapeTwoSmallTen) : ShapeTwoSmallEleven := by
  intro G _ _ L Q n z u h d T hn
  rcases Nat.lt_or_ge n 11 with h11 | h11
  · exact h10 G L Q n z u h d T (by omega)
  · obtain rfl : n = 11 := by omega
    obtain ⟨e⟩ := h.iso
    exact false_of_shapeTwo_eleven htri hGLS hO hEO hR2 h d T e

end Main

end CFSG.OddStandard.AltStdSec
