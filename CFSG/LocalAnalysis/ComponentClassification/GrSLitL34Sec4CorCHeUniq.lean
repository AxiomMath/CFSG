module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitGeneral
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCSteps
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCTypes
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitReduction

public section

namespace CFSG.ComponentClassification.GSThmB.CorC

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {X : Type} [Group X] [Finite X]

theorem held_equiv_of_unbalancing
    (hTB : GSLit.ThompsonBurgoyneInput) (hSA : SolAltLit.SolomonAlternatingOddInput)
    [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {b y : X} {M : Subgroup X}
    (hUM : GSUnbalancingTriple b y M) (hHe : GrSLit.IsHeldType (M ⧸ Open.fusionZStar M)) :
    Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* Blueprint.NativeSporadic.He) := by
  obtain ⟨hb, -, -, hMb, hMc, -, -⟩ := gsUnbalancingTriple_iff.mp hUM
  obtain ⟨eH⟩ := hHe
  have hcH : Nat.card (↥M ⧸ Open.fusionZStar ↥M) = 4030387200 := by
    rw [Nat.card_congr eH.toEquiv, Sporadic.He.card_He]
  rcases hTB X hnonab hK hz hU b y M hUM with ⟨n, hodd, hn, he⟩ |
      (h7 | ⟨p, f, hp, hp2, -, -, hL⟩) | (hHe' | h34)
  · exact absurd ⟨b, M, n, hb, hodd, hn, hMb, hMc, he⟩ (hSA X hnonab hK hz hU)
  · exfalso
    have hZ := fusionZStar_eq_of_alternating h7
    obtain ⟨e7⟩ := h7
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZ).toEquiv, Nat.card_congr e7.toEquiv,
      GSThmB.card_alternatingGroup_seven] at hcH
    norm_num at hcH
  · exfalso
    have hs := FooteLit.isSimpleGroup_of_lieModel_psl_two hL
    have hcard := GSThmB.card_of_lieModel_psl_two hp2 hL
    have hq : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
    have hZ := GrSLit.fusionZStar_eq_pPrimeCore_of_simple hs (fusionZStar_ne_top (by omega))
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZ).toEquiv, hcard] at hcH
    exact ordA_one_ne_held hq hcH
  · exact hHe'
  · exfalso
    have h20160 := (PSL3Four.excludes_alternating_models_stated.{0} _
      (GSLit.statedClassicalModel_of_lieModel_psl_three h34)).1
    omega

end CFSG.ComponentClassification.GSThmB.CorC
