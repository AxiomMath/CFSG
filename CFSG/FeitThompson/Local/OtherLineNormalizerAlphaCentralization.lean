module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.OtherLineNormalizerPlaneProduct
import CFSG.FeitThompson.Local.KappaResidualFixedSpaceAndPrimeOrder
import CFSG.FeitThompson.Representations.TypePOrientedCoreFamily
import CFSG.FeitThompson.Local.AlphaSigmaPrimeSeparation
import CFSG.FeitThompson.Local.NormalImageConfinesCoprimeCommutators
import CFSG.FeitThompson.Local.SigmaNormalizerNonconjugateMaximal
import CFSG.FeitThompson.Local.FittingSupportExcludesNormalCore
import CFSG.FeitThompson.Definitions.AlphaCore
import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
import CFSG.FeitThompson.Definitions.LocalComplementaryPrimeConstraint
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
public import Mathlib
import CFSG.FeitThompson.Representations.InducedFamilyIrreducibleRowOrthogonal

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson
open CFSG.FeitThompson.Prep08
open Subgroup Pointwise

universe u

theorem FTS_other_line_normalizer_alpha_centralization
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FPL_low_rank_sylow_central_product.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_other_line_normalizer_alpha_centralization.{u} := by
  intro G _ _ hG M T A A0 p hs hpσ hpα
  have hp : p.Prime := hs.prime
  have hfp := Fact.mk hp
  have hsimple : IsSimpleGroup G := hG.isSimpleGroup
  set K : Subgroup G := alphaCoreOf M ⊓ T with hKdef
  obtain ⟨hAT, hnorm⟩ :=
    FTS_other_line_normalizer_plane_product h₁ h₂ h₃ h₄ G hG M T A A0 p hs
  have hAlphaNorm : M ≤ normalizer ((alphaCoreOf M : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (alphaCoreOf_le M)).1
      (by rw [subgroupOf_alphaCoreOf]; exact alphaCore_normal ↥M)
  have hAK : A ≤ normalizer ((K : Subgroup G) : Set G) :=
    le_trans (le_inf (hs.le.trans hAlphaNorm) (hAT.trans Subgroup.le_normalizer))
      Subgroup.inf_normalizer_le_normalizer_inf
  have hKT : K ≤ T := inf_le_right
  have hAlphaPi : IsPiSubgroup (alphaPrimes ↥M) (alphaCoreOf M) :=
    isPiSubgroup_map_subtype_iff.2 (isPiSubgroup_alphaCore ↥M)
  have hKpi : IsPiSubgroup (alphaPrimes ↥M) K := hAlphaPi.of_le inf_le_left
  have hcop : Nat.Coprime (Nat.card ↥(K.subgroupOf T)) p := by
    have hcard : Nat.card ↥(K.subgroupOf T) = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKT).toEquiv
    rw [hcard]
    refine Nat.Coprime.symm (hp.coprime_iff_not_dvd.2 fun hdvd => hpα ?_)
    exact isPiSubgroup_iff.1 hKpi p (Nat.mem_primeFactors.2 ⟨hp, hdvd, Nat.card_pos.ne'⟩)
  have hApg : IsPGroup p ↥(A.subgroupOf T) := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAT).toEquiv]; exact hs.isPlane.natCard)
  have hDA : (((sigmaCore T).subgroupOf T) ⊔ (A.subgroupOf T)).Normal := by
    rw [← Subgroup.subgroupOf_sup (sigmaCore_le T) hAT]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le (sigmaCore_le T) hAT)).2 hnorm
  have hKA : A.subgroupOf T ≤ normalizer ((K.subgroupOf T : Subgroup ↥T) : Set ↥T) :=
    OrientedCoreFamily.le_normalizer_subgroupOf hAK
  have hkey := commutator_le_inf_of_sup_normal (D := (sigmaCore T).subgroupOf T)
    (A := A.subgroupOf T) (K := K.subgroupOf T) hp hApg hDA hcop hKA
  have hmapS := Subgroup.map_mono (f := T.subtype) (hkey.trans inf_le_right)
  rw [map_subtype_commutator_subgroupOf hKT hAT,
    Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le T)] at hmapS
  have hmapK := Subgroup.map_mono (f := T.subtype) (hkey.trans inf_le_left)
  rw [map_subtype_commutator_subgroupOf hKT hAT, Subgroup.map_subgroupOf_eq_of_le hKT] at hmapK
  have hA0card : Nat.card ↥A0 = p := hs.natCard_A0
  have hMTconj : ∀ g : G, MulAut.conj g • M ≠ T := by
    refine conj_smul_ne_of_normalizer_le hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hs.isCoatom_M hs.isCoatom_T hs.ne hpσ ?_
      (hs.le_A.trans hs.le) ?_ hs.normalizer_le
    · refine bot_lt_iff_ne_bot.2 fun h => ?_
      rw [h, Subgroup.card_bot] at hA0card
      exact hp.one_lt.ne hA0card
    · exact IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hA0card)
  have hdisj : ∀ r ∈ alphaPrimes ↥M, r ∉ sigmaPrimes T := fun r hr =>
    notMem_sigmaPrimes_of_mem_alphaPrimes_of_not_conj hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hs.isCoatom_M hs.isCoatom_T hMTconj hr
  have hbot : ⁅K, A⁆ = ⊥ :=
    eq_bot_of_isPiSubgroup_of_isPiSubgroup hdisj (hKpi.of_le hmapK)
      ((isPiSubgroup_sigmaCore T).of_le hmapS)
  rw [Subgroup.commutator_comm]
  exact hbot

end

end CFSG.FeitThompson.Proofs
