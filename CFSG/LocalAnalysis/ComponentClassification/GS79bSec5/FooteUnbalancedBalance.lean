module

public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FooteUnbalanced
import CFSG.LocalAnalysis.ComponentClassification.GrSLitLocalBalanceCase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitCases
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGWBridge
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCorollaryC
import CFSG.LocalAnalysis.ComponentClassification.FooteLitGeneral
import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedHe
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixA
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixB
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL2Balance
import CFSG.LocalAnalysis.ComponentClassification.GrSLitLocalBalanceHe

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.GSLit
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem locallyTwoBalancedAt_of_inputs_of_footeUnbalanced (hTB : ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput) (hS : SchreierFor Blueprint.Catalog)
    (hBR : TheoremBReachInput) (hCorC : GSThmB.CorollaryCStatement) (hH : HarrisInput)
    (hFU : FooteLit.FooteMaximalUnbalancedInput)
    (hHSF : HarrisSolomonFritzInput) (hCI : ClassicalInvolutionInput)
    (hSol : SolomonCommutingCoreInput)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) : LocallyTwoBalancedAt X := by
  rintro J ⟨x, y, hT⟩ a ha hJa hJ E hE hE4
  obtain ⟨hx, -, -, hJx, hJxp, -⟩ := id hT
  rcases hTB X hnonab hK hz hU x y J hT with ⟨n, hodd, hn, he⟩ |
      (h7 | ⟨p, f, hp, hp2, -, -, hL⟩) | (hHe | h34)
  · exact absurd ⟨x, J, n, hx, hodd, hn, hJx, hJxp, he⟩ (hSA X hnonab hK hz hU)
  · exact commutator_wGroup_le_of_alternating_seven hCorC hSol hnonab hK hz hU ha hJa hJ h7 hE
      hE4
  · have hR := gsRestrictedType_of_gsUnbalancingTriple_of_footeUnbalanced hTB hSA hS
      hBR hH hFU hHSF hCI
      (heldFixedInput_of_inner HeldFix.isL34Type_of_isPComponent_centralizer_heA0
          HeldFix.not_isPComponent_centralizer_heT1P) l34FixedInput a7FixedInput
      l2FixedInput hnonab hK hz hU hT
    have hs := FooteLit.isSimpleGroup_of_lieModel_psl_two hL
    have hcard := GSThmB.card_of_lieModel_psl_two hp2 hL
    have hq : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
    rcases hR with hHe' | h34' | h7' | h5' | h7''
    · exfalso
      obtain ⟨eH⟩ := hHe'
      have hc : Nat.card (J ⧸ Open.fusionZStar J) = 4030387200 := by
        rw [Nat.card_congr eH.toEquiv, Sporadic.He.card_He]
      have hZ := fusionZStar_eq_pPrimeCore_of_simple hs (fusionZStar_ne_top_of_card (by omega))
      rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZ).toEquiv, hcard] at hc
      exact ordA_one_ne_held_of_odd hq hc
    · exact (false_of_psl34_of_psl_two h34' hp2 hL).elim
    · exfalso
      obtain ⟨e7⟩ := h7'
      have hc : Nat.card (J ⧸ Open.fusionZStar J) = 2520 := by
        rw [Nat.card_congr e7.toEquiv, GSThmB.card_alternatingGroup_seven]
      have hZ := fusionZStar_eq_pPrimeCore_of_simple hs (fusionZStar_ne_top_of_card (by omega))
      rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZ).toEquiv, hcard] at hc
      exact GSThmB.ordA_one_ne_2520 _ hc
    · exact commutator_wGroup_le_of_l2 hJa hJ (Or.inl h5') hE hE4
    · exact commutator_wGroup_le_of_l2 hJa hJ (Or.inr h7'') hE hE4
  · exact commutator_wGroup_le_of_held hJa hJ hHe hE hE4
  · exact commutator_wGroup_le_of_psl34 hJa hJ h34 hE hE4

theorem localBalanceCase_of_footeUnbalanced (hTB : ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput) (hS : SchreierFor Blueprint.Catalog)
    (hBR : TheoremBReachInput) (hCorC : GSThmB.CorollaryCStatement) (hH : HarrisInput)
    (hFU : FooteLit.FooteMaximalUnbalancedInput)
    (hHSF : HarrisSolomonFritzInput) (hCI : ClassicalInvolutionInput)
    (hSol : SolomonCommutingCoreInput) : LocalBalanceCase := by
  intro X _ _ _ hnonab hK hz hU
  exact locallyTwoBalanced_of_gwTwoBalanced (gwTwoBalanced_of_locallyTwoBalancedAt hSol
    (locallyTwoBalancedAt_of_inputs_of_footeUnbalanced hTB hSA hS hBR hCorC hH hFU hHSF hCI hSol hnonab hK hz hU))

end CFSG.ComponentClassification.GrSLit
