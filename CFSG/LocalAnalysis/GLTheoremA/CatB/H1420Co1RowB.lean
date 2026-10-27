module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K14SporRows1
import CFSG.HardMathSupport.Dickson.BMRows.CensusB3
import CFSG.HardMathSupport.Dickson.BMRows.RowsB

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint CFSG.Monster.GMS
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal


theorem cardRow_B_of_seven_dvd
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) {n : ℕ}
    (h7 : 7 ∣ n) (hn : n ≠ 64561751654400) : K14Spor.CardRow n .B := by
  obtain ⟨hfin, hs, ⟨b⟩, hnc⟩ := CFSG.HardMathSupport.Dickson.BMRows.model_B
  refine @K14Spor.cardRow_of_model n .B NativeSporadic.B _ hfin hs hOut b hnc ?_
  intro k hk
  by_cases hinv : ∃ d : NativeSporadic.B, BabyInv 0 d ∧ d * k * d⁻¹ = k⁻¹
  ·
    obtain ⟨d, hd, hdk⟩ := hinv
    rcases CFSG.HardMathSupport.Dickson.BMRows.CensusB3.shapeRkAt'_fi22_of_inverted
        CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
        CFSG.HardMathSupport.Dickson.I271.tabBThreeACard_thm hk hd hdk with
      hno | ⟨J, hJ, hu, ⟨e⟩, -⟩
    · exact fun I hI => absurd hI (hno I)
    · intro I hI hc
      rw [hu I hI] at hc
      obtain ⟨f⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
      apply hn
      rw [← hc, Nat.card_congr e.toEquiv, ← Nat.card_congr f.toEquiv]
      exact CFSG.Sporadic.Fi22.card_Fi22
  ·
    have hunv : ∀ d : NativeSporadic.B, BabyInv 0 d → d * k * d⁻¹ ≠ k⁻¹ :=
      fun d hd h => hinv ⟨d, hd, h⟩
    have hnot0 : ¬ IsConj k (phiB (t3 0)) := by
      intro hc
      obtain ⟨d, hd, hdr⟩ := phiB_t3_zero_inverted
      obtain ⟨c, hcx⟩ := isConj_iff.1 hc
      refine hunv (c⁻¹ * d * c) (BabyInv.of_isConj hd (isConj_iff.2 ⟨c⁻¹, by simp⟩)) ?_
      have hx' : k = c⁻¹ * phiB (t3 0) * c := by rw [← hcx]; group
      calc c⁻¹ * d * c * k * (c⁻¹ * d * c)⁻¹
          = c⁻¹ * (d * phiB (t3 0) * d⁻¹) * c := by rw [hx']; group
        _ = k⁻¹ := by rw [hdr, hx']; group
    have hsc : IsConj k (phiB (t3 1)) := by
      obtain ⟨i, hi⟩ := bThree_classes k hk
      fin_cases i
      · exact absurd hi hnot0
      · exact hi
      · exact absurd (hi.trans bThreeRc_holds) hnot0
      · exact hi.trans bThreeRd_holds
    refine K14Spor.noCardComp_of_not_dvd ?_
    rw [CFSG.Monster.Existence.natCard_centralizer_eq_of_isConj hsc]
    exact fun h => bThreeB_seven_free (h7.trans h)

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
