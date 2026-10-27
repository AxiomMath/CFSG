module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitGeneral
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma514G
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCTypes
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitReduction

public section

namespace CFSG.ComponentClassification.GSThmB.CorC

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem gsFixedLayer_perfect (M : Subgroup X) (e : X) :
    ⁅gsFixedLayer M e, gsFixedLayer M e⁆ = gsFixedLayer M e := by
  rw [gsFixedLayer, ← map_commutator, pLayer_two_isPerfect]

theorem alternating_equiv_of_unbalancing
    (hTB : GSLit.ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput) [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {b y : X} {M : Subgroup X}
    (hUM : GSUnbalancingTriple b y M)
    (h7 : Nonempty (M ⧸ Open.fusionZStar M ≃* alternatingGroup (Fin 7))) :
    Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨hb, -, -, hMb, hMc, -, -⟩ := gsUnbalancingTriple_iff.mp hUM
  obtain ⟨e7⟩ := h7
  have hc7 : Nat.card (↥M ⧸ Open.fusionZStar ↥M) = 2520 := by
    rw [Nat.card_congr e7.toEquiv, GSThmB.card_alternatingGroup_seven]
  rcases hTB X hnonab hK hz hU b y M hUM with ⟨n, hodd, hn, he⟩ |
      (h7' | ⟨p, f, hp, hp2, -, -, hL⟩) | (hHe | h34)
  · exact absurd ⟨b, M, n, hb, hodd, hn, hMb, hMc, he⟩ (hSA X hnonab hK hz hU)
  · exact h7'
  · exfalso
    have hs := FooteLit.isSimpleGroup_of_lieModel_psl_two hL
    have hcard := GSThmB.card_of_lieModel_psl_two hp2 hL
    have hZ := GrSLit.fusionZStar_eq_pPrimeCore_of_simple hs (fusionZStar_ne_top (by omega))
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZ).toEquiv, hcard] at hc7
    exact GSThmB.ordA_one_ne_2520 _ hc7
  · exfalso
    obtain ⟨eH⟩ := hHe
    have hs : IsSimpleGroup (↥M ⧸ pPrimeCore 2 ↥M) :=
      @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.He.isSimpleGroup_He eH
    have hZ := GrSLit.fusionZStar_eq_pPrimeCore_of_simple hs (fusionZStar_ne_top (by omega))
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZ).toEquiv,
      Nat.card_congr eH.toEquiv, Sporadic.He.card_He] at hc7
    norm_num at hc7
  · exfalso
    have h20160 := (PSL3Four.excludes_alternating_models_stated.{0} _
      (GSLit.statedClassicalModel_of_lieModel_psl_three h34)).1
    omega

end CFSG.ComponentClassification.GSThmB.CorC
