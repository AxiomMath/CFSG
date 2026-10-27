module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.TypUSL

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

theorem typU_of_psp_case (hI : Phase1Inputs) {H : Type} [Group H] [Finite H]
    (hH : SectionRank.IsKGroupCat H) {M : Subgroup H} {x : H} {T : Subgroup H} {w : H}
    (h : VCSetting M x T w) (hT : LieModel (↥T ⧸ Open.fusionZStar ↥T) .PSp 2 3 1) :
    TypU ↥M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hChev : HarrisLit.IsSimpleChevalleyOver 3 (↥M ⧸ Open.fusionZStar ↥M) :=
    hI.p8 H hH M h.hM x h.ox h.hxM T h.hTM h.hTx h.hT hT w h.ow h.hwT h.hwZ
  by_cases hIn : GH74.GLS.InChev2 (↥M ⧸ Open.fusionZStar ↥M)
  ·
    have hT2 : HarrisLit.IsTwoQuasisimple ↥T :=
      ((HarrisLit.isTwoComponentIn_iff h.hTx).mpr h.hT).2.2
    have hdvd : Nat.card (↥T ⧸ Open.fusionZStar ↥T) ∣
        Nat.card (↥M ⧸ Open.fusionZStar ↥M) :=
      card_quot_fusionZStar_dvd h.hTM hT2
    have hcardT : Nat.card (↥T ⧸ Open.fusionZStar ↥T) = 25920 :=
      card_lieModel_psp_two_three_one hT
    have hdvd' : 25920 ∣ Nat.card (↥M ⧸ Open.fusionZStar ↥M) := by
      rwa [hcardT] at hdvd
    rcases hI.chevOdd (↥M ⧸ Open.fusionZStar ↥M) 3 Nat.prime_three (by norm_num) hChev hIn with
      hmem | hA6 | hPSp
    ·
      have hmem' : Nat.card (↥M ⧸ Open.fusionZStar ↥M) = 60 ∨
          Nat.card (↥M ⧸ Open.fusionZStar ↥M) = 168 ∨
          Nat.card (↥M ⧸ Open.fusionZStar ↥M) = 6048 := by
        simpa using hmem
      rcases hmem' with h60 | h168 | h6048
      · exact absurd (h60 ▸ hdvd') (not_dvd_of_psp_card (Or.inl rfl))
      · exact absurd (h168 ▸ hdvd') (not_dvd_of_psp_card (Or.inr (Or.inl rfl)))
      · exact absurd (h6048 ▸ hdvd')
          (not_dvd_of_psp_card (Or.inr (Or.inr (Or.inr rfl))))
    ·
      have h360 : Nat.card (↥M ⧸ Open.fusionZStar ↥M) = 360 :=
        card_lieModel_psl_two_three_two hA6
      exact absurd (h360 ▸ hdvd')
        (not_dvd_of_psp_card (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inl hPSp))
  · exact Or.inr (Or.inl ⟨3, Nat.prime_three, by norm_num, hChev, hIn⟩)

theorem verticalCentral_typU (hI : Phase1Inputs) : GS82PumpInputs.VerticalCentral TypU := by
  intro H _ _ hH M hM x hx hxM T hTM hTx hT hTyp w hw hwT hwZ
  have h : VCSetting M x T w := ⟨hM, hx, hxM, hTM, hTx, hT, hw, hwT, hwZ⟩
  rcases hTyp with ⟨q, hq, h9, hSL⟩ | ⟨r, hr, hr2, hChev⟩ | hPSp | ⟨n, hn7, hDC⟩
  · exact typU_of_slTwo_case hI hH h hq h9 hSL
  · exact Or.inr (Or.inl ⟨r, hr, hr2,
      GSThmB.verticalCentral_typChev hI.p2 hr hr2 H hH M hM x hx hxM T hTM hTx hT hChev
        w hw hwT hwZ⟩)
  · exact typU_of_psp_case hI hH h hPSp
  · obtain ⟨m, hnm, hDCm⟩ :=
      hI.p5 H hH M hM x hx hxM T hTM hTx hT n hn7 hDC w hw hwT hwZ
    exact Or.inr (Or.inr (Or.inr ⟨m, le_trans hn7 hnm, hDCm⟩))

end CFSG.OddStandard.SmallF3.HypA2
