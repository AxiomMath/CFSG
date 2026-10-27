module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoTwoExCent
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoTwoExClose
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoCaseI
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoThirteen
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.OddStandard.AltStdCycTwo.Two.Exact

open Subgroup Equiv Equiv.Perm AltStdBal AltStdSec CFSG.ComponentClassification.RankTwoStandard
  CFSG.ComponentClassification.RestrictedStd.Spor CFSG.RankThree.PartOne

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ} {z u : G}

theorem dichotomy_of_cent_large (htri : ExactShapeTrichotomy) (hR2 : RankTwoAlternatingStandard)
    (hlookup : AltComponentLookup) (hHN : HNLocalComponentsInput)
    (hOut : SporadicOuterOrderLeTwoSimple) (hFour : FourExactOuterInput)
    (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (hC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q)
    (hbal : FourPointBalance L θ) (hn : 15 ≤ n) :
    CaseII θ T.hn (L ⊔ zpowers u) z ∨ CaseII θ T.hn (L ⊔ zpowers (u * z)) z ∨
      ∃ H : Subgroup G, WreathPair L z n H := by
  classical
  let S₀ : Finset (Fin n) := {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩}
  have hS₀ : S₀.card = 3 := by
    simp only [S₀]
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · simp [Fin.ext_iff]
    · simp [Fin.ext_iff]
  have hex : ExactShape z L n := exactShape_of_cent T.toBase hC
  have ht : z ∈ centralizer (corr (X := G) θ (altSub S₀) : Set G) :=
    t_mem_centralizer_corr (X := G) θ hex (altSub S₀)
  have hsec := exactShape_section_three hex θ hS₀ (by omega) ht
  have hKcat : CFSG.SectionRank.IsKGroupCat (Sec G (corr (X := G) θ (altSub S₀))) :=
    isKGroupCat_sec (isKGroupCat_of_kProper T.std.kProper)
      (centralizer_ne_top_of_exists_ne_one T.std (exists_ne_one_of_card_ge_three θ (by omega)))
  have hO := oddCore_sec_eq_bot (corr (X := G) θ (altSub S₀))
  rcases htri _ _ _ (n - S₀.card) (by omega) hKcat hO hsec with h1 | h1 | h1 | h1
  · exact (false_of_caseI_w htri hlookup hHN hOut hFour T θ (by omega) (by omega) (Or.inl hS₀)
      (by omega) ⟨ht, h1⟩).elim
  · obtain ⟨H, hH⟩ := exists_wreathPair_of_caseIII_root hex θ (by omega) hS₀ ⟨ht, h1⟩
    exact Or.inr (Or.inr ⟨H, hH⟩)
  · rcases caseII_of_double htri hR2 T θ hC hbal (by omega) (by omega) (Or.inl hS₀) (by omega)
      ⟨ht, h1⟩ with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl h2)
  · omega

theorem dichotomy_of_cent_thirteen (htri : ExactShapeTrichotomy)
    (hR2 : RankTwoAlternatingStandard) (hlookup : AltComponentLookup)
    (hHN : HNLocalComponentsInput) (hOut : SporadicOuterOrderLeTwoSimple)
    (hFour : FourExactOuterInput) (T : Shape G L Q 13 z u) (θ : L ≃* alternatingGroup (Fin 13))
    (hC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q)
    (hbal : FourPointBalance L θ) :
    CaseII θ T.hn (L ⊔ zpowers u) z ∨ CaseII θ T.hn (L ⊔ zpowers (u * z)) z ∨
      ∃ H : Subgroup G, WreathPair L z 13 H := by
  classical
  obtain ⟨S₀, S₁, hS₀, hS₁, hS01⟩ : ∃ S₀ S₁ : Finset (Fin 13),
      S₀.card = 3 ∧ S₁.card = 4 ∧ S₀ ⊆ S₁ :=
    ⟨{0, 1, 2}, {0, 1, 2, 3}, by decide, by decide, by decide⟩
  have hex : ExactShape z L 13 := exactShape_of_cent T.toBase hC
  have hK := isKGroupCat_of_kProper T.std.kProper
  have ht₁ : z ∈ centralizer (corr (X := G) θ (altSub S₁) : Set G) :=
    t_mem_centralizer_corr (X := G) θ hex (altSub S₁)
  have hsec₁ := exactShape_section_root hex θ (by omega) (by omega) ht₁
  have hKcat₁ : CFSG.SectionRank.IsKGroupCat (Sec G (corr (X := G) θ (altSub S₁))) :=
    isKGroupCat_sec hK
      (centralizer_ne_top_of_exists_ne_one T.std (exists_ne_one_of_card_ge_three θ (by omega)))
  have hO₁ := oddCore_sec_eq_bot (corr (X := G) θ (altSub S₁))
  rcases htri _ _ _ (13 - S₁.card) (by omega) hKcat₁ hO₁ hsec₁ with h1 | hW₁ | h1 | h1
  · exact (false_of_caseI_w htri hlookup hHN hOut hFour T θ (by norm_num) (by norm_num)
      (Or.inr hS₁) (by omega) ⟨ht₁, h1⟩).elim
  ·
    have ht₀ : z ∈ centralizer (corr (X := G) θ (altSub S₀) : Set G) :=
      t_mem_centralizer_corr (X := G) θ hex (altSub S₀)
    have hsec₀ := exactShape_section_three hex θ hS₀ (by omega) ht₀
    have hKcat₀ : CFSG.SectionRank.IsKGroupCat (Sec G (corr (X := G) θ (altSub S₀))) :=
      isKGroupCat_sec hK
        (centralizer_ne_top_of_exists_ne_one T.std (exists_ne_one_of_card_ge_three θ (by omega)))
    have hO₀ := oddCore_sec_eq_bot (corr (X := G) θ (altSub S₀))
    rcases htri _ _ _ (13 - S₀.card) (by omega) hKcat₀ hO₀ hsec₀ with h2 | h2 | h2 | ⟨-, h2⟩
    · exact (false_of_caseI_w htri hlookup hHN hOut hFour T θ (by norm_num) (by norm_num)
        (Or.inl hS₀) (by omega) ⟨ht₀, h2⟩).elim
    · obtain ⟨H, hH⟩ := exists_wreathPair_of_caseIII_root hex θ (by norm_num) hS₀ ⟨ht₀, h2⟩
      exact Or.inr (Or.inr ⟨H, hH⟩)
    · rcases caseII_of_double htri hR2 T θ hC hbal (by norm_num) (by norm_num) (Or.inl hS₀)
        (by omega) ⟨ht₀, h2⟩ with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (Or.inl h3)
    ·
      exfalso
      have hdvd := (sq_card_dvd_of_wreath (by omega) hW₁).trans
        (card_sec_dvd_of_le (corr_mono θ (altSub_mono hS01)))
      rw [card_eq_of_hnOutcome h2, hS₁] at hdvd
      revert hdvd
      norm_num [Nat.factorial]
  · rcases caseII_of_double htri hR2 T θ hC hbal (by norm_num) (by norm_num) (Or.inr hS₁)
      (by omega) ⟨ht₁, h1⟩ with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl h2)
  · omega

end CFSG.OddStandard.AltStdCycTwo.Two.Exact

namespace CFSG.OddStandard.AltStdCycTwo

open Subgroup CFSG.ComponentClassification.RankTwoStandard
  CFSG.ComponentClassification.RestrictedStd.Spor CFSG.RankThree.PartOne

theorem cycTwoShapeTwoLargeFalse_of_centInf
    (hC : ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
      (θ : L ≃* alternatingGroup (Fin n)) (z : G), OrderTwo G L Q n θ z → 13 ≤ n →
        centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q)
    (htri : AltStdSec.ExactShapeTrichotomy) (hR2 : RankTwoAlternatingStandard)
    (hlookup : AltStdSec.AltComponentLookup) (hHN : HNLocalComponentsInput)
    (hOut : SporadicOuterOrderLeTwoSimple) (hFour : FourExactOuterInput) :
    CycTwoShapeTwoLargeFalse := by
  intro G _ _ L Q n θ z u O hn hu huL hu2
  have T := Two.Shape.of_orderTwo O hu huL hu2
  have hCz := hC G L Q n θ z O hn
  rcases eq_or_ne n 13 with rfl | h13
  · exact Two.Exact.false_of_dichotomy_of_cent htri T θ hCz (by norm_num)
      (Two.Exact.dichotomy_of_cent_thirteen htri hR2 hlookup hHN hOut hFour T θ hCz O.bal4)
  · have hn15 : 15 ≤ n := by
      obtain ⟨k, rfl⟩ := O.odd
      omega
    exact Two.Exact.false_of_dichotomy_of_cent htri T θ hCz (by omega)
      (Two.Exact.dichotomy_of_cent_large htri hR2 hlookup hHN hOut hFour T θ hCz O.bal4 hn15)

end CFSG.OddStandard.AltStdCycTwo
