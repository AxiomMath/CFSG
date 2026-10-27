module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.CommonSylowNormalizerBetaFactor
import CFSG.FeitThompson.Local.CommonSylowNormalizerTauOneTransfer
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerEmbeddingSylows
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerOutsideComplement
import CFSG.FeitThompson.Local.ResidualComplementNilpotentCore
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.OddOrder.SigmaSylowIsAmbientSylow
import CFSG.FeitThompson.OddOrder.SigmaPrimesWellDefined
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

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson CFSG.FeitThompson

universe u

variable {G : Type u} [Group G] [Finite G] {q p : ℕ}

theorem mem_sigmaPrimes_of_prime_order_le_inf
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (hG : IsOddOrderMinimalSimple G) {M T : Subgroup G} (hM : IsCoatom M) (hT : IsCoatom T)
    (hMT : M ≠ T) (hq : q.Prime) (hqσ : q ∈ sigmaPrimes M)
    {Y : Subgroup G} (hYM : Y ≤ M) (hY : Y ≠ ⊥) (hYq : IsPGroup q ↥Y)
    (hYT : normalizer (Y : Set G) ≤ T) (hp : p.Prime) (hpT : p ∈ sigmaPrimes T)
    {P : Subgroup G} (hPJ : P ≤ M ⊓ T) (hPcard : Nat.card ↥P = p) :
    q ∈ sigmaPrimes T := by
  have : Fintype G := Fintype.ofFinite G
  by_contra hqT
  obtain ⟨-, -, hsd⟩ :=
    FBG_sigma_prime_normalizer_outside_complement h₂ h₃ h₅ G hG M T hM hT hMT q hq hqσ Y hYM hY
      hYq hYT hqT
  refine notMem_of_isHallPiSubgroupOf_of_dvd_index (h₁ G hG T hT).1 hp ?_ hpT
  rw [index_subgroupOf_left_eq hsd]
  exact hPcard ▸ Subgroup.card_dvd_of_le hPJ

theorem exists_sylow_normalizer_le_inf
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (hG : IsOddOrderMinimalSimple G) {M T : Subgroup G} (hM : IsCoatom M) (hT : IsCoatom T)
    (hMT : M ≠ T) (hq : q.Prime) (hqσ : q ∈ sigmaPrimes M) (hqT : q ∈ sigmaPrimes T)
    {Y : Subgroup G} (hYM : Y ≤ M) (hY : Y ≠ ⊥) (hYq : IsPGroup q ↥Y)
    (hYT : normalizer (Y : Set G) ≤ T) :
    ∃ Q : Sylow q G, normalizer ((Q : Subgroup G) : Set G) ≤ M ⊓ T := by
  have : Fintype G := Fintype.ofFinite G
  have := Fact.mk hq
  obtain ⟨S, hYS, hS⟩ := exists_isSylowSubgroupOf_ge hq
    (le_inf hYM (Subgroup.le_normalizer.trans hYT)) hYq
  obtain ⟨-, hsyl, -⟩ :=
    FBG_sigma_prime_normalizer_embedding_sylows h₅ G hG M T hM hT hMT q hq hqσ Y hYM hY hYq hYT
  obtain ⟨hNM, hST⟩ := hsyl S hS hYS
  obtain ⟨-, R, hRT, hRcard, hRN⟩ := (mem_sigmaPrimes_iff_exists_subgroup hq).1 hqT
  have hNT : normalizer (S : Set G) ≤ T :=
    normalizer_le_of_normalizer_le_of_card_eq hq hRT hRcard hST.1 hST.2 hRN
  have hcard : Nat.card ↥S = q ^ (Nat.card G).factorization q :=
    natCard_eq_pow_factorization_of_mem_sigmaPrimes hqT hST.1 hST.2
  exact ⟨Sylow.ofCard S hcard, by rw [Sylow.coe_ofCard]; exact le_inf hNM hNT⟩

theorem FBG_sigma_prime_normalizer_first_prime_embedding
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_beta_prime_centralizing_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FBG_sigma_prime_normalizer_first_prime_embedding.{u} := by
  intro G _ _ hG M T hM hT hMT q hq hqσ Y hYM hY hYq hYT p hp _hpτ hpT P hPJ hPcard
  have hqT : q ∈ sigmaPrimes T :=
    mem_sigmaPrimes_of_prime_order_le_inf h₁ h₂ h₃ h₅ hG hM hT hMT hq hqσ hYM hY hYq
      hYT hp hpT hPJ hPcard
  obtain ⟨Q, hNQ⟩ := exists_sylow_normalizer_le_inf h₅ hG hM hT hMT hq hqσ hqT hYM hY hYq hYT
  have hGA : IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨-, hαβ, hAB, hBne⟩ :=
    FBG_common_sylow_normalizer_beta_factor h₁ h₄ h₆ G hGA M T hM hT hMT q hq Q hNQ
  have hNQ' : normalizer ((Q : Subgroup G) : Set G) ≤ T ⊓ M := by rw [inf_comm]; exact hNQ
  obtain ⟨hTfac, -, -, -⟩ :=
    FBG_common_sylow_normalizer_beta_factor h₁ h₄ h₆ G hGA T M hT hM (Ne.symm hMT) q hq Q hNQ'
  rw [inf_comm] at hTfac
  exact ⟨hqT, fun h => hBne (hAB.symm.trans h), hαβ, hTfac,
    FBG_common_sylow_normalizer_tau_one_transfer h₁ h₄ h₆ G hGA M T hM hT hMT q hq Q hNQ⟩

end

end CFSG.FeitThompson.Proofs
