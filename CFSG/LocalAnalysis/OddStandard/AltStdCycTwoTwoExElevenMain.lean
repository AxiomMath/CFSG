module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoTwoExElevenCent
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoTwoExElevenClose
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoCaseI
public import CFSG.LocalAnalysis.OddStandard.AltStdSecOverEleven
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarSecSeven
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoThirteen

public section

namespace CFSG.OddStandard.AltStdCycTwo.Two.Exact

open Subgroup AltStdSec
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput LieOrderFormulasInput)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}

section Unique

theorem caseIIIAt_of_wreathPair_eleven_of_exact (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) (hS : StandardSetting G L) (hex : ExactShape z L 11)
    (e : L ≃* alternatingGroup (Fin 11)) {H : Subgroup G} (hH : WreathPair L z 11 H)
    {S : Finset (Fin 11)} (hS3 : S.card = 3) : CaseIIIAt e z S := by
  classical
  have ht : z ∈ centralizer (corr (X := G) e (altSub S) : Set G) :=
    t_mem_centralizer_corr (X := G) e hex (altSub S)
  have hm8 : 11 - S.card = 8 := by omega
  have hsec := exactShape_section_three hex e hS3 (by omega) ht
  rw [hm8] at hsec
  have hKcat : CFSG.SectionRank.IsKGroupCat (Sec G (corr (X := G) e (altSub S))) :=
    isKGroupCat_sec (isKGroupCat_of_kProper hS.kProper)
      (centralizer_ne_top_of_exists_ne_one hS (exists_ne_one_of_card_ge_three e (by omega)))
  have hOS := oddCore_sec_eq_bot (corr (X := G) e (altSub S))
  obtain ⟨f₁, f₂, hf₁, hf₂, hcomm, hswap⟩ := exists_sec_pair e (by norm_num) hH hS3 ht
  obtain ⟨eB⟩ := exists_equiv_corr_altSub (X := G) e Sᶜ
  have hm : Sᶜ.card = 8 := by rw [card_compl_fin S]; omega
  have hcardB : Nat.card ↥(corr (X := G) e (altSub Sᶜ)) = 20160 := by
    rw [card_eq_of_equiv_alt (by omega) eB, hm]
    decide
  have hcen : center ↥(corr (X := G) e (altSub Sᶜ)) = ⊥ := center_eq_bot_of_alt (by omega) eB
  let Φ := f₁.noncommCoprod f₂ (fun a b => hcomm a b)
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have hab' : f₁ a * f₂ b = 1 := hab
    have h2b : f₁ a = f₂ b⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_left hab'
    have hacen : a ∈ center ↥(corr (X := G) e (altSub Sᶜ)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply hf₁
      rw [map_mul, map_mul, h2b]
      exact hcomm g b⁻¹
    rw [hcen, Subgroup.mem_bot] at hacen
    have hb1 : f₂ b = 1 := by
      have := hab'
      rw [hacen, map_one, one_mul] at this
      exact this
    exact Prod.ext hacen (hf₂ (hb1.trans (map_one f₂).symm))
  have h49 : 49 ∣ Nat.card (Sec G (corr (X := G) e (altSub S))) := by
    have := Subgroup.card_dvd_of_injective Φ hΦ
    rw [Nat.card_prod, hcardB] at this
    exact Nat.dvd_trans (by norm_num) this
  rcases central_or_wreath_eight hGLS hO hKcat hOS hsec h49 with h1 | h2
  · exfalso
    have hff : ∀ b, f₂ b = f₁ b := by
      intro b
      rw [hswap b]
      have := Subgroup.mem_center_iff.1 h1 (f₁ b)
      rw [← this]
      exact mul_inv_cancel_right _ _
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_alt (by omega) eB
    apply hab
    apply hf₁
    rw [map_mul, map_mul]
    have := hcomm a b
    rwa [hff b] at this
  · refine ⟨ht, ?_⟩
    rw [hm8]
    exact h2

theorem wreathPair_unique_eleven_of_exact (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) (hS : StandardSetting G L) (hex : ExactShape z L 11)
    {H₁ H₂ : Subgroup G} (h₁ : WreathPair L z 11 H₁) (h₂ : WreathPair L z 11 H₂) :
    H₂ = H₁ ∨ H₂ = H₁.map (MulAut.conj z).toMonoidHom := by
  obtain ⟨e⟩ := hex.iso
  have hS₀ : ({0, 1, 2} : Finset (Fin 11)).card = 3 := by decide
  exact wreath_unique_of_caseIII_root hex e (by norm_num) hS₀
    (caseIIIAt_of_wreathPair_eleven_of_exact hGLS hO hS hex e h₁ hS₀) h₁ h₂

theorem exactWreathUnique_eleven (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) : ExactWreathUnique G 11 :=
  fun _ _ hS hex _ _ h₁ h₂ => wreathPair_unique_eleven_of_exact hGLS hO hS hex h₁ h₂

end Unique

end CFSG.OddStandard.AltStdCycTwo.Two.Exact

namespace CFSG.OddStandard.AltStdCycTwo.Two.Exact

open Subgroup Equiv Equiv.Perm AltStdSec CFSG.ComponentClassification.RankTwoStandard
  CFSG.ComponentClassification.RestrictedStd.Spor CFSG.RankThree.PartOne
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput LieOrderFormulasInput
  EvenLieOuterTwoComponentsInput)

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {z u : G}

theorem dichotomy_of_cent_eleven (htri : ExactShapeTrichotomy)
    (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    (hEO : EvenLieOuterTwoComponentsInput) (hR2 : RankTwoAlternatingStandard)
    (hlookup : AltComponentLookup) (hHN : HNLocalComponentsInput)
    (hOut : SporadicOuterOrderLeTwoSimple) (hFour : FourExactOuterInput)
    (T : Shape G L Q 11 z u) (θ : L ≃* alternatingGroup (Fin 11))
    (hC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q)
    (hbal : FourPointBalance L θ) :
    CaseII θ T.hn (L ⊔ zpowers u) z ∨ CaseII θ T.hn (L ⊔ zpowers (u * z)) z ∨
      ∃ H : Subgroup G, WreathPair L z 11 H := by
  classical
  obtain ⟨S₀, S₁, hS₀, hS₁, hS01⟩ : ∃ S₀ S₁ : Finset (Fin 11),
      S₀.card = 3 ∧ S₁.card = 4 ∧ S₀ ⊆ S₁ :=
    ⟨{0, 1, 2}, {0, 1, 2, 3}, by decide, by decide, by decide⟩
  have hex : ExactShape z L 11 := exactShape_of_cent T.toBase hC
  have hK := isKGroupCat_of_kProper T.std.kProper
  have hL0 : ∀ (O : OverData G z 10) {R : Subgroup (Perm (Fin (10 + 3)))}, SecR 10 R →
      CFSG.SectionRank.IsKGroupCat ↥(centralizer (secP O R : Set G)) → L0Normal O R :=
    fun O {_} hR hKR => l0Normal_ten O hR hGLS hO hEO rfl hKR
  have ht₁ : z ∈ centralizer (corr (X := G) θ (altSub S₁) : Set G) :=
    t_mem_centralizer_corr (X := G) θ hex (altSub S₁)
  have hm7 : 11 - S₁.card = 7 := by omega
  have hsec₁ := exactShape_section_root hex θ (by omega) (by omega) ht₁
  rw [hm7] at hsec₁
  have hKcat₁ : CFSG.SectionRank.IsKGroupCat (Sec G (corr (X := G) θ (altSub S₁))) :=
    isKGroupCat_sec hK
      (centralizer_ne_top_of_exists_ne_one T.std (exists_ne_one_of_card_ge_three θ (by omega)))
  have hO₁ := oddCore_sec_eq_bot (corr (X := G) θ (altSub S₁))
  rcases exactShape_trichotomy_seven hGLS hO hEO hKcat₁ hO₁ hsec₁ with h1 | hW₁ | h1
  · exact (false_of_caseI_w htri hlookup hHN hOut hFour T θ (by norm_num) (by norm_num)
      (Or.inr hS₁) (by omega) ⟨ht₁, h1⟩).elim
  ·
    have ht₀ : z ∈ centralizer (corr (X := G) θ (altSub S₀) : Set G) :=
      t_mem_centralizer_corr (X := G) θ hex (altSub S₀)
    have hm8 : 11 - S₀.card = 8 := by omega
    have hsec₀ := exactShape_section_three hex θ hS₀ (by omega) ht₀
    rw [hm8] at hsec₀
    have hKcat₀ : CFSG.SectionRank.IsKGroupCat (Sec G (corr (X := G) θ (altSub S₀))) :=
      isKGroupCat_sec hK
        (centralizer_ne_top_of_exists_ne_one T.std (exists_ne_one_of_card_ge_three θ (by omega)))
    have hO₀ := oddCore_sec_eq_bot (corr (X := G) θ (altSub S₀))
    have h49 : 49 ∣ Nat.card (Sec G (corr (X := G) θ (altSub S₀))) := by
      have hdvd := (sq_card_dvd_of_wreath (by norm_num) hW₁).trans
        (card_sec_dvd_of_le (corr_mono θ (altSub_mono hS01)))
      exact Nat.dvd_trans (by norm_num [Nat.factorial]) hdvd
    rcases central_or_wreath_eight hGLS hO hKcat₀ hO₀ hsec₀ h49 with h2 | h2
    · exact (false_of_caseI_w htri hlookup hHN hOut hFour T θ (by norm_num) (by norm_num)
        (Or.inl hS₀) (by omega) ⟨ht₀, h2⟩).elim
    · obtain ⟨H, hH⟩ := exists_wreathPair_of_caseIII_root hex θ (by norm_num) hS₀
        ⟨ht₀, by rw [hm8]; exact h2⟩
      exact Or.inr (Or.inr ⟨H, hH⟩)
  · rcases caseII_of_double_of_l0 hR2 (m := 10) T θ hC hbal (by norm_num) hL0 (Or.inr hS₁)
      (by omega) ⟨ht₁, by rw [hm7]; exact h1⟩ with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl h2)

end CFSG.OddStandard.AltStdCycTwo.Two.Exact

namespace CFSG.OddStandard.AltStdCycTwo

open Subgroup CFSG.ComponentClassification.RankTwoStandard
  CFSG.ComponentClassification.RestrictedStd.Spor CFSG.RankThree.PartOne
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput LieOrderFormulasInput
  EvenLieOuterTwoComponentsInput)

theorem cycTwoShapeTwoElevenFalse_of_centInf
    (hC : ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G)
      (θ : L ≃* alternatingGroup (Fin 11)) (z : G), OrderTwo G L Q 11 θ z →
        centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q)
    (htri : AltStdSec.ExactShapeTrichotomy) (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) (hEO : EvenLieOuterTwoComponentsInput)
    (hR2 : RankTwoAlternatingStandard) (hlookup : AltStdSec.AltComponentLookup)
    (hHN : HNLocalComponentsInput) (hOut : SporadicOuterOrderLeTwoSimple)
    (hFour : FourExactOuterInput) :
    CycTwoShapeTwoElevenFalse := by
  intro G _ _ L Q θ z u O hu huL hu2
  have T := Two.Shape.of_orderTwo O hu huL hu2
  have hCz := hC G L Q θ z O
  exact Two.Exact.false_of_dichotomy_of_unique_cent (Two.Exact.exactWreathUnique_eleven hGLS hO)
    T θ hCz (by norm_num)
    (Two.Exact.dichotomy_of_cent_eleven htri hGLS hO hEO hR2 hlookup hHN hOut hFour T θ hCz O.bal4)

end CFSG.OddStandard.AltStdCycTwo
