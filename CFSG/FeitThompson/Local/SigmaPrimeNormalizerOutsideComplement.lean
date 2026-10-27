module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerEmbeddingSylows
import CFSG.FeitThompson.Local.NoncyclicSigmaNormalizer
import CFSG.FeitThompson.Local.AbelianHallTauTwoControlsCentralizers
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived
import CFSG.FeitThompson.Local.QuotientFittingInvariantComplement
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
import CFSG.FeitThompson.Local.MetacyclicOddGroupUniqueTorsionPlane
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson CFSG.FeitThompson

universe u

variable {G : Type u} [Group G]

theorem exists_isInternalSemidirectProduct_sigmaCore_ge [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable ↥H) {T A : Subgroup G} (hT : IsCoatom T)
    (hAT : A ≤ T) (hA : IsPiSubgroup ((sigmaPrimes T)ᶜ) A) :
    ∃ F : Subgroup G, A ≤ F ∧ FreeCore.IsInternalSemidirectProduct T (sigmaCore T) F := by
  have : Group.IsSolvable ↥T := hsolv T hT.1
  have hA' : IsPiSubgroup ((sigmaPrimes T)ᶜ) (A.subgroupOf T) := by
    refine isPiSubgroup_iff.2 fun p hp => isPiSubgroup_iff.1 hA p ?_
    rwa [Nat.card_congr (subgroupOfEquivOfLe hAT).toEquiv] at hp
  obtain ⟨H, hH, hAH⟩ := exists_isHallSubgroup_ge_of_isPiSubgroup hA'
  have hcomap : (H.map T.subtype).subgroupOf T = H :=
    Subgroup.comap_map_eq_self_of_injective T.subtype_injective H
  have hkey := sup_eq_and_inf_eq_bot_of_isHallSubgroup_compl (π := sigmaPrimes T)
    (sigmaCore_le T) (Subgroup.map_subtype_le H)
    (isHallSubgroup_subgroupOf_sigmaCore hna hodd hsolv hT) (by rwa [hcomap])
    ((Subgroup.map_subtype_le H).trans (le_normalizer_sigmaCore T))
  refine ⟨H.map T.subtype, ?_, ⟨hkey.1, le_normalizer_sigmaCore T, disjoint_iff.2 hkey.2⟩⟩
  have := Subgroup.map_mono (f := T.subtype) hAH
  rwa [Subgroup.map_subgroupOf_eq_of_le hAT] at this

theorem FBG_sigma_prime_normalizer_outside_complement
    (h₁ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u}) :
    _root_.CFSG.FeitThompson.Statements.FBG_sigma_prime_normalizer_outside_complement.{u} := by
  intro G _ _ hG M T hM hT hMT q hq hqσ Y hYM hY hYq hYT hqT
  have := hG.isSimpleGroup
  have hG04 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG08 : Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  obtain ⟨-, hsyl, hqcase⟩ :=
    FBG_sigma_prime_normalizer_embedding_sylows h₃ G hG M T hM hT hMT q hq hqσ Y hYM hY hYq hYT
  have hqτ : q ∈ tauTwoPrimes T := hqcase.resolve_left hqT
  have hrank : elementaryAbelianPRank q ↥T = 2 := (mem_tauTwoPrimes_iff.1 hqτ).2.2
  have hYTle : Y ≤ T := Subgroup.le_normalizer.trans hYT
  obtain ⟨S, hYS, hS⟩ := exists_isSylowSubgroupOf_ge hq (le_inf hYM hYTle) hYq
  obtain ⟨-, hST⟩ := hsyl S hS hYS
  obtain ⟨A, hAS, hAelem, hAcard⟩ :=
    exists_isElementaryAbelian_natCard_eq_sq_le_of_isSylow hq hST.1 hST.2 hrank
  have hAMT : A ≤ M ⊓ T := hAS.trans hS.1
  have hAT : A ≤ T := hAMT.trans inf_le_right
  have hAM : A ≤ M := hAMT.trans inf_le_left
  have hplane : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane q T A :=
    ⟨hT, hq, hqT, hAT, nonempty_mulEquiv_pi_of_isElementaryAbelian hq hAelem hAcard⟩
  have hdisj : sigmaCore T ⊓ M = ⊥ := h₂ G hG04 q T A M hplane hM hMT hAM
  refine ⟨hqτ, hdisj, ?_⟩
  have hApi : IsPiSubgroup ((sigmaPrimes T)ᶜ) A := by
    refine isPiSubgroup_iff.2 fun p hp => ?_
    rw [hAcard, Nat.primeFactors_pow _ two_ne_zero, hq.primeFactors, Finset.mem_singleton] at hp
    exact hp ▸ hqT
  obtain ⟨F, hAF, hsd⟩ := exists_isInternalSemidirectProduct_sigmaCore_ge
    hG.not_isMulCommutative hG.odd_natCard hG.isSolvable_of_ne_top hT hAT hApi
  have hFN : F ≤ normalizer (A : Set G) := (h₁ G hG04 q T A F hplane ⟨hT, hsd⟩ hAF).1
  have hAnc : ¬ IsCyclic ↥A :=
    not_isCyclic_of_natCard_eq_prime_sq_of_pow_eq_one hq hAcard
      (fun x hx => (isElementaryAbelian_iff.1 hAelem).2 x hx) le_rfl
  have hNAM : normalizer (A : Set G) ≤ M :=
    FTS_noncyclic_sigma_normalizer h₃ G hG08 M A q hM hqσ hAM hAelem.isPGroup hAnc
  have hFMT : F ≤ M ⊓ T := le_inf (hFN.trans hNAM) hsd.right_le
  have hMTF : M ⊓ T ≤ F := by
    intro z hz
    obtain ⟨s, hs, f, hf, rfl⟩ := hsd.exists_mul (mem_inf.1 hz).2
    have hfM : f ∈ M := (mem_inf.1 (hFMT hf)).1
    have hsM : s ∈ M := by
      have hrw : s = s * f * f⁻¹ := by group
      rw [hrw]
      exact M.mul_mem (mem_inf.1 hz).1 (M.inv_mem hfM)
    have hs1 : s = 1 := by
      have := hdisj ▸ (mem_inf.2 ⟨hs, hsM⟩ : s ∈ sigmaCore T ⊓ M)
      simpa using this
    rw [hs1, one_mul]
    exact hf
  have hMTeq : M ⊓ T = F := le_antisymm hMTF hFMT
  rw [hMTeq]
  exact hsd

end

end CFSG.FeitThompson.Proofs
