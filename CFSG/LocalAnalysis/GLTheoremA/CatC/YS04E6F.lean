module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04E6FTw
public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04F

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration TauCeti
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.GLTheoremA.YS04E6F (meets_inner_E6_untw meets_inner_E6_tw)


theorem kd26fE6_holds : YS04F.KD26fE6 := by
  intro S _ _ _ _ q lin hS h3 D hD
  refine YS04F.card_le_of_meets_inner Nat.prime_three (inner S) ?_ D hD
  intro D' hD' hc
  obtain ⟨i, hi, ⟨e⟩⟩ := hS
  cases i with
  | cyclic _ _ => simp [onLie] at hi
  | alternating _ _ => simp [onLie] at hi
  | sporadic _ => simp [onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases lin with
    | true =>
      cases d <;> simp only [onLie, isE6Eps] at hi
      rename_i qq
      obtain ⟨K, _, _, hK, -, ⟨φ⟩⟩ :=
        exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 qq hv
      have h3K : 3 ∣ Nat.card K - 1 := by
        rw [hK, hi]
        simpa [qEps] using h3
      exact CFSG.HardMathSupport.Timmesfeld.Tables.T1b.meets_inner_of_mulEquiv_mulAut
        (e.trans φ) (fun D hD hc => meets_inner_E6_untw h3K D hD hc) D' hD' (by simpa using hc)
    | false =>
      cases d <;> simp only [onLie, isE6Eps] at hi
      rename_i qq
      obtain ⟨K, _, σ, hK, hσ, ⟨φ⟩⟩ := exists_catEquiv_twistedE6 qq hv
      haveI : Finite K := Nat.finite_of_card_ne_zero (by
        rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ qq.prime_p.ne_zero))
      have h3' : 3 ∣ qq.p ^ qq.exponent + 1 := by
        have : qq.p ^ qq.exponent = q := by rw [← hi, TauCeti.PrimePower.card_def]
        rw [this]
        simpa [qEps] using h3
      exact CFSG.HardMathSupport.Timmesfeld.Tables.T1b.meets_inner_of_mulEquiv_mulAut
        (e.trans φ) (fun D hD hc => meets_inner_E6_tw σ qq.prime_p qq.exponent_pos hK hσ h3' D hD
          (by simpa using hc)) D' hD' (by simpa using hc)

end CFSG.LocalAnalysis.GLTheoremA
