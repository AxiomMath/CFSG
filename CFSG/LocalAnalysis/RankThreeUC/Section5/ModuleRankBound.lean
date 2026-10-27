module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.BinaryActionRankAlternatives
public import CFSG.LocalAnalysis.RankThreeUC.Section5.CommRankDef
import CFSG.LocalAnalysis.RankThreeUC.Section5.CaseB2
import CFSG.LocalAnalysis.RankThreeUC.Section5.FittingCentralizingInvolutionDisplacement
import CFSG.LocalAnalysis.RankThreeUC.Section5.InvolutionDisplacementReduction
import CFSG.LocalAnalysis.RankThreeUC.Section5.NotIsPrimePowTwoPowSubOne
import CFSG.LocalAnalysis.RankThreeUC.Section5.PCoreEqBotOfFaithfulIrreducible
import CFSG.LocalAnalysis.RankThreeUC.Section5.PNoncentralizingInvolutionDisplacement
import CFSG.LocalAnalysis.RankThreeUC.Section5.TwoPowLeCardDelta
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

theorem lt_commRank_of_orderOf_eq_two_of_symmetry (hc : BinaryActionRankCounterexample G p P T B e ρ)
    (hsym : ∀ q ∈ alphaSet G, ∃ P' : Subgroup G, BinaryActionRankCounterexample G q P' T B e ρ) {t : G}
    (ht : orderOf t = 2) : e + 1 < commRank ρ t := by
  have hF := hc.faithfulBinaryIrreducibleAction
  by_cases htF : ∀ x ∈ CFSG.fittingSubgroup G, t * x = x * t
  · exact lt_commRank_of_centralizes_fittingSubgroup hc (lt_card_Delta hc) ht htF
  obtain ⟨q, hq, -, hOt⟩ := InvolutionDisplacementReduction.exists_prime_commutator_ne_bot
    (pCore_eq_bot_of_faithful_irreducible 2 ρ hF.faithful hF.irreducible) htF
  by_cases hqα : q ∈ alphaSet G
  · obtain ⟨P', hc'⟩ := hsym q hqα
    by_cases htP' : t ∈ Subgroup.centralizer (P' : Set G)
    · rw [commRank_eq_fixedQuot_finrank]
      exact alphaPrimeInvolutionBound_holds G V ρ q P' T B e hc' (not_isPrimePow_two_pow_sub_one hc')
        (map_conj_eq_of_mem_normalizer_commutator hc') (commutator_mem_normalizer_and_mul_self_mem_normalizer hc')
        (two_pow_le_card_Delta hc') t ht htP' hOt
    · exact lt_commRank_of_not_mem_centralizer_of_orderOf_eq_two hc' ht htP'
  · exact lt_commRank_of_not_mem_alphaSet hc ht hq hqα hOt

theorem lt_moduleM_of_symmetry (hc : BinaryActionRankCounterexample G p P T B e ρ)
    (hsym : ∀ q ∈ alphaSet G, ∃ P' : Subgroup G, BinaryActionRankCounterexample G q P' T B e ρ) :
    e + 1 < moduleM ρ := by
  by_cases hev : Even (Nat.card G)
  · obtain ⟨t, -, ht, hm⟩ := exists_involution_in_sylow_attaining_moduleM ρ T
      hc.faithfulBinaryIrreducibleAction.sylow hev
    rw [← hm]
    exact lt_commRank_of_orderOf_eq_two_of_symmetry hc hsym ht
  · have hM : moduleM ρ = Module.finrank (ZMod 2) V := by
      unfold moduleM
      rw [if_neg hev]
    rw [hM]
    have h1 := two_mul_card_Delta_le_finrank hc
    have h2 := lt_card_Delta hc
    omega

theorem false_of_symmetry (hc : BinaryActionRankCounterexample G p P T B e ρ)
    (hsym : ∀ q ∈ alphaSet G, ∃ P' : Subgroup G, BinaryActionRankCounterexample G q P' T B e ρ) : False :=
  hc.not_concl (Or.inl (lt_moduleM_of_symmetry hc hsym))

end CFSG.LocalAnalysis.RankThreeUC.Section5
