module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupEight
public import CFSG.LocalAnalysis.OddStandard.AltStdSecOverCase3
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupEightLinear

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput LieOrderFormulasInput)


theorem central_or_wreath_eight (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    {X : Type} [Group X] [Finite X] {t : X} {A : Subgroup X} (hK : CFSG.SectionRank.IsKGroupCat X)
    (hOX : CFSG.oddCore X = ⊥) (h : ExactShape t A 8) (h49 : 49 ∣ Nat.card X) :
    t ∈ center X ∨ WreathOutcome t A 8 := by
  rcases section_dichotomy hOX h (by norm_num) with h1 | h2 | h3
  · exact Or.inl h1
  · exact Or.inr h2
  exfalso
  rcases exactShape_almostSimple_eight hGLS hO hK hOX h h3 with ⟨e, -⟩ |
      ⟨W, hWN, hCW, -, ⟨eW⟩⟩ | ⟨W, hWN, hCW, -, hLie⟩
  · have hc : Nat.card X = 3628800 := by
      rw [← Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin]
      decide
    rw [hc] at h49
    omega
  · have := hWN
    have hout : Nat.card (Outer W) ≤ 2 :=
      CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.SmallOddCore.hs_outer_card_le
        (eW.trans CFSG.Sporadic.Schreier.hsPermEquiv)
    have hidx : W.index ≤ 2 := (index_le_card_outer W hCW).trans hout
    have hW : Nat.card W = 44352000 := (Nat.card_congr eW.toEquiv).trans CFSG.Sporadic.HS.card_HS
    rw [← W.card_mul_index, hW] at h49
    have h0 : W.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    obtain ⟨k, hk⟩ : ∃ k, W.index = k := ⟨_, rfl⟩
    rw [hk] at h49 hidx h0
    interval_cases k <;> omega
  · have := hWN
    obtain ⟨K, _iK, _fK, hK4, ⟨eW⟩⟩ := exists_projectiveSL_of_lieModel_four hLie
    have hout : Nat.card (Outer W) ∣ 4 := by
      rw [Nat.card_congr (equivalence eW).toEquiv]
      exact card_outer_dvd_four hK4
    have hidx : W.index ≤ 4 :=
      (index_le_card_outer W hCW).trans (Nat.le_of_dvd (by norm_num) hout)
    have hW : Nat.card W = 987033600 := by
      rw [CFSG.SeitzReduction.LinearPilot.card_of_lieModel_PSL_two hLie]
      simp [CFSG.Open.ordA, Finset.prod_Icc_succ_top]
    rw [← W.card_mul_index, hW] at h49
    have h0 : W.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    obtain ⟨k, hk⟩ : ∃ k, W.index = k := ⟨_, rfl⟩
    rw [hk] at h49 hidx h0
    interval_cases k <;> omega

theorem caseIIIAt_of_wreathPair_eleven {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {z : G}
    (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput) (h : Setting G L 11)
    (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) (e : L ≃* alternatingGroup (Fin 11)) {H : Subgroup G}
    (hH : WreathPair L z 11 H) {S : Finset (Fin 11)} (hS : S.card = 3) : CaseIIIAt e z S := by
  classical
  have hex : ExactShape z L 11 := exactShape_of_setting h d hQ2
  have ht : z ∈ centralizer (corr (X := G) e (altSub S) : Set G) :=
    t_mem_centralizer_corr (X := G) e hex (altSub S)
  have hm8 : 11 - S.card = 8 := by omega
  have hsec := exactShape_section_three hex e hS (by omega) ht
  rw [hm8] at hsec
  have hKcat : CFSG.SectionRank.IsKGroupCat (Sec G (corr (X := G) e (altSub S))) :=
    isKGroupCat_sec (isKGroupCat_of_kProper h.std.kProper)
      (centralizer_ne_top_of_ne_one h (exists_ne_one_of_card_ge_three e (by omega)))
  have hOS := oddCore_sec_eq_bot (corr (X := G) e (altSub S))
  obtain ⟨f₁, f₂, hf₁, hf₂, hcomm, hswap⟩ := exists_sec_pair e (by norm_num) hH hS ht
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

theorem wreathPairUniqueAt_eleven (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) : WreathPairUniqueAt 11 := by
  intro G _ _ L Q z h d hQ2 H₁ H₂ h₁ h₂
  obtain ⟨e⟩ := h.iso
  have hS₀ : ({0, 1, 2} : Finset (Fin 11)).card = 3 := by decide
  exact wreath_unique_of_caseIII_root (exactShape_of_setting h d hQ2) e (by norm_num) hS₀
    (caseIIIAt_of_wreathPair_eleven hGLS hO h d hQ2 e h₁ hS₀) h₁ h₂

end CFSG.OddStandard.AltStdSec
