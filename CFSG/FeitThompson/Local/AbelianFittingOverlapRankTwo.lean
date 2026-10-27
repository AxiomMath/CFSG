module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.NonTIFittingNilpotentCoreBetaExclusion
import CFSG.FeitThompson.Local.FittingOverlapPrimeCentralizerSmall
import CFSG.FeitThompson.Local.KappaFixedSubgroupDerivedAndHall
import CFSG.FeitThompson.Local.NonabelianAmbientPlaneCentralizer
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane
import CFSG.FeitThompson.Local.CyclicCentralizerFactorRestriction
import CFSG.FeitThompson.Local.PrimeFreeFactorizationFixedSubgroupTransport
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.Foundations.SolvableHallExistence
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib
import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise _root_.CFSG.FeitThompson

universe u

variable {G : Type u} [Group G] [Finite G] {M X Y : Subgroup G} {g : G} {p : ℕ}

theorem pCoreIn_le_sigmaCore (hp : p.Prime) (hpσ : p ∈ sigmaPrimes M) :
    pCoreIn p M ≤ sigmaCore M := by
  refine le_sigmaCore (pCoreIn_le p M) ?_ ?_
  · rw [pCoreIn_eq, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    exact pCore_normal p ↥M
  · exact ((isPiSubgroup_singleton_iff hp _).2 (isPGroup_pCoreIn hp M)).mono
      (Set.singleton_subset_iff.2 hpσ)

theorem two_le_maxElementaryAbelianPRank_hallCoreIn (hG : IsFBGAmbient G)
    (hsetup : IsFittingOverlapSetup M X g) (hHS : hallCoreIn M = sigmaCore M)
    (hXS : X ≤ sigmaCore M) : 2 ≤ maxElementaryAbelianPRank ↥(hallCoreIn M) := by
  have := hG.isSimpleGroup
  have h1lt : 1 < Nat.card ↥X :=
    lt_of_le_of_ne Nat.card_pos (Ne.symm fun h => hsetup.ne_bot (Subgroup.card_eq_one.1 h))
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.2 h1lt
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ Nat.card ↥X := Nat.dvd_of_mem_primeFactors hp
  have hpσ : p ∈ sigmaPrimes M :=
    isPiSubgroup_iff.1 ((isPiSubgroup_sigmaCore M).of_le hXS) p hp
  have hodd : Odd p :=
    odd_of_prime_of_dvd_odd hpp hG.odd_natCard
      (hpdvd.trans (Subgroup.card_subgroup_dvd_card X))
  have hXeq : ((fittingRaw ↥M).map M.subtype ⊓
      ((fittingRaw ↥M).map M.subtype).map (MulAut.conj g⁻¹ : G →* G) : Subgroup G) = X := by
    rw [hsetup.eq, mixedFitting_eq, conjSubgroup_eq]
  have hnc : ¬ IsCyclic ↥(pCoreIn p M) := by
    rw [pCoreIn_eq]
    exact not_isCyclic_map_pCore_of_dvd_natCard_inf_fittingRaw_conj hG.not_isMulCommutative
      hsetup.isCoatom hsetup.notMem hpp (by rw [hXeq]; exact hpdvd)
  have hOle : pCoreIn p M ≤ hallCoreIn M := by
    rw [hHS]; exact pCoreIn_le_sigmaCore hpp hpσ
  calc 2 ≤ elementaryAbelianPRank p ↥(pCoreIn p M) :=
        two_le_elementaryAbelianPRank_of_not_isCyclic hpp hodd (isPGroup_pCoreIn hpp M) hnc
    _ ≤ elementaryAbelianPRank p ↥(hallCoreIn M) :=
        elementaryAbelianPRank_le_of_le hpp.one_lt hOle
    _ ≤ maxElementaryAbelianPRank ↥(hallCoreIn M) :=
        elementaryAbelianPRank_le_maxElementaryAbelianPRank hpp

theorem maxElementaryAbelianPRank_hallCoreIn_le_two
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_nilpotent_sigma_core_fitting_structure.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_prime_subgroup_unique_maximum.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (hG : IsFBGAmbient G) (hsetup : IsFittingOverlapSetup M X g)
    (hHS : hallCoreIn M = sigmaCore M) (hXS : X ≤ sigmaCore M)
    (habelian : IsMulCommutative ↥(hallCoreIn M)) :
    maxElementaryAbelianPRank ↥(hallCoreIn M) ≤ 2 := by
  have h1lt : 1 < Nat.card ↥X :=
    lt_of_le_of_ne Nat.card_pos (Ne.symm fun h => hsetup.ne_bot (Subgroup.card_eq_one.1 h))
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.2 h1lt
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  obtain ⟨w, hwX, hwo⟩ := exists_mem_orderOf_eq_of_dvd hpp (Nat.dvd_of_mem_primeFactors hp)
  have hLcard : Nat.card ↥(zpowers w) = p := by rw [Nat.card_zpowers, hwo]
  have hLX : (zpowers w : Subgroup G) ≤ X := zpowers_le.2 hwX
  have hbound := (_root_.CFSG.FeitThompson.Proofs.FBG_fitting_overlap_prime_centralizer_small
    h₁ h₂ h₃ h₇ h₈ G hG M X g hsetup p hpp (zpowers w) hLX hLcard).2.2.1
  have hLH : (zpowers w : Subgroup G) ≤ hallCoreIn M := by rw [hHS]; exact hLX.trans hXS
  have heq : centralizerWithin (hallCoreIn M) (zpowers w) = hallCoreIn M := by
    rw [centralizerWithin_eq]
    exact inf_eq_left.2 (le_centralizer_of_isMulCommutative_of_le habelian hLH)
  rwa [heq] at hbound

theorem commutator_commutator_eq_bot_of_isMulCommutative
    (hprod : IsInternalDirectProduct (mixedFitting M) (sigmaCore M) Y)
    (hS : IsMulCommutative ↥(sigmaCore M)) (hY : IsCyclic ↥Y)
    (hM'F : (⁅M, M⁆ : Subgroup G) ≤ mixedFitting M) :
    ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ = ⊥ := by
  have := hS
  have := hY.isMulCommutative
  have hF : IsMulCommutative ↥(mixedFitting M) := hprod.isMulCommutative
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hM'F.trans (le_centralizer_of_isMulCommutative_of_le hF hM'F)

theorem kappaPrimes_eq_empty_of_commutator_commutator_eq_bot
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_local_pair.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_trivial_residual_prime_fixed_core.{u})
    (hG : IsFBGAmbient G) (hM : IsCoatom M)
    (hM'' : ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ = ⊥) : kappaPrimes M = ∅ := by
  by_contra hne
  obtain ⟨q, hq⟩ := Set.nonempty_iff_ne_empty.2 hne
  have hqp : q.Prime := prime_of_mem_kappaPrimes hq
  have : Group.IsSolvable ↥M := hG.isSolvable M hM.1
  obtain ⟨K₀, hK₀⟩ := exists_isHallSubgroup (X := ↥M) (kappaPrimes M)
  have hKsub : (K₀.map M.subtype).subgroupOf M = K₀ :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hqdvd : q ∣ Nat.card ↥K₀ := by
    have hcard : Nat.card ↥K₀ * K₀.index = Nat.card ↥M := Subgroup.card_mul_index K₀
    rcases (Nat.Prime.dvd_mul hqp).1 (hcard ▸ dvd_natCard_of_mem_kappaPrimes hq) with h | h
    · exact h
    · exact absurd hq (isPiNumber_iff.1 hK₀.index q (Nat.mem_primeFactors.2 ⟨hqp, h,
        Subgroup.index_ne_zero_of_finite⟩))
  have hKbot : K₀.map M.subtype ≠ ⊥ := by
    intro hbot
    have hone : Nat.card ↥K₀ = 1 := by
      rw [← Subgroup.card_map_of_injective (K := K₀) M.subtype_injective, hbot,
        Subgroup.card_bot]
    exact hqp.one_lt.ne' (Nat.eq_one_of_dvd_one (hone ▸ hqdvd))
  obtain ⟨hAne, -, hAle, -⟩ :=
    _root_.CFSG.FeitThompson.Proofs.FBG_kappa_fixed_subgroup_derived_and_hall h₂ h₄ h₅ h₆ G hG M
      (K₀.map M.subtype) hM hKbot (Subgroup.map_subtype_le _)
      (by rw [hKsub]; exact hK₀.isHallPiSubgroup)
  refine hAne (le_bot_iff.1 ?_)
  rw [← hM'']
  exact hAle.trans inf_le_right

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open CFSG.FeitThompson Subgroup

universe u

theorem FBG_abelian_fitting_overlap_rank_two
    (h₁ : Statements.FBG_nilpotent_sigma_core_fitting_structure.{u})
    (h₂ : Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₃ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₄ : Statements.FNI_kappa_local_pair.{u})
    (h₅ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₆ : Statements.FNI_kappa_trivial_residual_prime_fixed_core.{u})
    (h₇ : Statements.FNI_nonabelian_prime_subgroup_unique_maximum.{u})
    (h₈ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FBG_abelian_fitting_overlap_rank_two.{u} := by
  intro G _ _ hG M X g hsetup habelian
  obtain ⟨Y, hY⟩ := exists_isSylowProduct (CFSG.FeitThompson.mixedFitting M)
    {p : ℕ | p.Prime ∧ p ∉ CFSG.FeitThompson.sigmaPrimes M}
  obtain ⟨-, hHS, hXS, -, hM'F, hprod, hYcyc, -⟩ :=
    FBG_nonti_fitting_nilpotent_core_and_beta_exclusion h₁ h₂ h₃ h₈ G hG M X g hsetup Y hY
  have hSab : IsMulCommutative ↥(CFSG.FeitThompson.sigmaCore M) := hHS ▸ habelian
  refine ⟨le_antisymm
    (maxElementaryAbelianPRank_hallCoreIn_le_two h₁ h₂ h₃ h₇ h₈ hG hsetup hHS hXS habelian)
    (two_le_maxElementaryAbelianPRank_hallCoreIn hG hsetup hHS hXS), ?_⟩
  exact kappaPrimes_eq_empty_of_commutator_commutator_eq_bot h₂ h₄ h₅ h₆ hG hsetup.isCoatom
    (commutator_commutator_eq_bot_of_isMulCommutative hprod hSab hYcyc hM'F)

end

end CFSG.FeitThompson.Proofs
