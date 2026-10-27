module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.L34False
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.SLTwo
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.TypU

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

theorem typU_of_slTwo_case (hI : Phase1Inputs) {H : Type} [Group H] [Finite H]
    (hH : SectionRank.IsKGroupCat H) {M : Subgroup H} {x : H} {T : Subgroup H} {w : H}
    (h : VCSetting M x T w) {q₁ : ℕ} (hq : Odd q₁) (h9 : 9 ≤ q₁)
    (hSL : HarrisLit.IsSLTwoOver q₁ (↥T ⧸ pPrimeCore 2 ↥T)) : TypU ↥M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : HarrisLit.IsTwoQuasisimple ↥T :=
    ((HarrisLit.isTwoComponentIn_iff h.hTx).mpr h.hT).2.2
  have hTcard : Nat.card (↥T ⧸ Open.fusionZStar ↥T) * 2 = q₁ * (q₁ ^ 2 - 1) :=
    card_quot_fusionZStar_of_isSLTwoOver hq hSL
  have hdvd : Nat.card (↥T ⧸ Open.fusionZStar ↥T) ∣
      Nat.card (↥M ⧸ Open.fusionZStar ↥M) :=
    card_quot_fusionZStar_dvd h.hTM hT2
  rcases hI.p7 H hH M h.hM x h.ox h.hxM T h.hTM h.hTx h.hT 9 q₁
      (by norm_num) (by norm_num) hq h9 hSL w h.ow h.hwT h.hwZ with
    ⟨q₂, hq₂odd, hq₂9, hq₂SL⟩ | hOdd | ⟨n, hn7, hn⟩ | ⟨hL34, _⟩
  · exact Or.inl ⟨q₂, hq₂odd, hq₂9, hq₂SL⟩
  ·
    rcases hOdd with ⟨τ, n, p, f, hp, hp2, _hadm, hm⟩
    have hChev : HarrisLit.IsSimpleChevalleyOver p (↥M ⧸ Open.fusionZStar ↥M) :=
      ⟨τ, n, f, hm⟩
    by_cases hIn : GH74.GLS.InChev2 (↥M ⧸ Open.fusionZStar ↥M)
    ·
      rcases hI.chevOdd (↥M ⧸ Open.fusionZStar ↥M) p hp hp2 hChev hIn with
        hmem | hA6 | hPSp
      ·
        have hmem' : Nat.card (↥M ⧸ Open.fusionZStar ↥M) = 60 ∨
            Nat.card (↥M ⧸ Open.fusionZStar ↥M) = 168 ∨
            Nat.card (↥M ⧸ Open.fusionZStar ↥M) = 6048 := by
          simpa using hmem
        rcases hmem' with h60 | h168 | h6048
        · exact absurd (h60 ▸ hdvd)
            (not_dvd_of_psl_card hq h9 hTcard (Or.inl rfl))
        · exact absurd (h168 ▸ hdvd)
            (not_dvd_of_psl_card hq h9 hTcard (Or.inr (Or.inl rfl)))
        · exact absurd (h6048 ▸ hdvd)
            (not_dvd_of_psl_card hq h9 hTcard (Or.inr (Or.inr rfl)))
      ·
        have hwM : w ∈ M := h.hTM h.hwT
        let w' : ↥M := ⟨w, hwM⟩
        have hw' : orderOf w' = 2 := by
          rw [Subgroup.orderOf_mk]
          exact h.ow
        have hwZ' : w' ∈ Open.fusionZStar ↥M := by
          obtain ⟨z, hz, hzw⟩ := Subgroup.mem_map.mp h.hwZ
          have hz' : z = w' := Subtype.ext hzw
          rwa [← hz']
        have hM2 : HarrisLit.IsTwoQuasisimple ↥M :=
          ((HarrisLit.isTwoComponent_iff_isPComponent M).mpr h.hM).2
        exact Or.inl ⟨9, by norm_num, by norm_num,
          isSLTwoOver_nine_of_psl_nine hI.griess hM2 hw' hwZ' hA6⟩
      · exact Or.inr (Or.inr (Or.inl hPSp))
    · exact Or.inr (Or.inl ⟨p, hp, hp2, hChev, hIn⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨n, hn7, hn⟩))
  ·
    exfalso
    by_cases hq9 : q₁ = 9
    · subst q₁
      exact false_of_l34_outcome hI.p11 h hSL hL34
    · have h11 : 11 ≤ q₁ := by
        obtain ⟨k, hk⟩ := hq
        omega
      have hpp : IsPrimePow q₁ := isPrimePow_of_isSLTwoOver hSL
      have hcardM : Nat.card (↥M ⧸ Open.fusionZStar ↥M) = 20160 := by
        calc Nat.card (↥M ⧸ Open.fusionZStar ↥M)
            = Nat.card ((↥M ⧸ pPrimeCore 2 ↥M) ⧸
                center (↥M ⧸ pPrimeCore 2 ↥M)) :=
              (Nat.card_congr (Sol78.coreQuotientCenterEquiv ↥M).toEquiv).symm
          _ = 20160 := card_lieModel_psl_three_two_two hL34
      exact (not_dvd_l34_of_psl_card hpp hq h11 hTcard) (hcardM ▸ hdvd)

end CFSG.OddStandard.SmallF3.HypA2
