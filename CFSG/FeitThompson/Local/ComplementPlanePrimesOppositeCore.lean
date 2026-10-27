module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.OutsideSigmaPlaneComplementNormality
import CFSG.FeitThompson.Local.AbelianHallTauTwoControlsCentralizers
import CFSG.FeitThompson.Local.OutsideSigmaPlaneComplementNormalizer
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

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson (mem_maximalSubgroups)
open CFSG.FeitThompson.Prep08 (IsPlaneAt IsMinimalSimpleOddOrder)

universe u

variable {G : Type*} [Group G] [Finite G]

theorem exists_isPlaneAt_le_of_isInternalSemidirectProduct_sigmaCore {T J : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hpσ : p ∉ sigmaPrimes T) (hJT : J ≤ T)
    (hsemi : FreeCore.IsInternalSemidirectProduct T (sigmaCore T) J)
    (hrank : elementaryAbelianPRank p ↥T = 2) :
    ∃ A : Subgroup G, A ≤ J ∧ IsPlaneAt p A := by
  have : Fact p.Prime := ⟨hp⟩
  have hfac : (Nat.card ↥T).factorization p = (Nat.card ↥J).factorization p :=
    factorization_natCard_eq_of_notMem_sigmaPrimes hp hpσ hJT hsemi.sup_eq hsemi.inf_eq_bot
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p ↥J))
  have hQJ : (Q : Subgroup ↥J).map J.subtype ≤ J := map_subtype_le _
  have hQcard : Nat.card ↥((Q : Subgroup ↥J).map J.subtype)
      = p ^ (Nat.card ↥T).factorization p := by
    rw [Subgroup.card_subtype, Q.card_eq_multiplicity, hfac]
  obtain ⟨A, hAQ, hAea, hAcard⟩ :=
    exists_isElementaryAbelian_natCard_eq_sq_le_of_isSylow hp (hQJ.trans hJT) hQcard hrank
  exact ⟨A, hAQ.trans hQJ, hAea, hAcard⟩

theorem mem_sigmaPrimes_of_mem_tauTwoPrimes_of_mem_sigmaCore_inf
    (h₂ : Statements.FTS_outside_sigma_plane_structure.{u})
    (G : Type u) [Group G] [Finite G] (hG : IsMinimalSimpleOddOrder G)
    {M T : Subgroup G} (hM : IsCoatom M) (hT : IsCoatom T)
    (hsemi : FreeCore.IsInternalSemidirectProduct T (sigmaCore T) (M ⊓ T))
    {x : G} (hxS : x ∈ sigmaCore M) (hxJ : x ∈ M ⊓ T) (hx1 : x ≠ 1)
    {p : ℕ} (hpτ : p ∈ tauTwoPrimes T) : p ∈ sigmaPrimes M := by
  have hp : p.Prime := prime_of_mem_tauTwoPrimes hpτ
  have hpσT : p ∉ sigmaPrimes T := notMem_sigmaPrimes_of_mem_tauTwoPrimes hpτ
  by_contra hpσM
  obtain ⟨A, hAJ, hplane⟩ := exists_isPlaneAt_le_of_isInternalSemidirectProduct_sigmaCore
    hp hpσT inf_le_right hsemi (elementaryAbelianPRank_eq_two_of_mem_tauTwoPrimes hpτ)
  have hnorm : (M ⊓ T : Subgroup G) ≤ normalizer (A : Set G) :=
    FTS_outside_sigma_plane_complement_normality h₂ G hG T A (M ⊓ T) p hT hp hpσT
      (hAJ.trans inf_le_right) hplane inf_le_right hsemi hAJ
  have hAM : A ≤ M := hAJ.trans inf_le_left
  have hSC : sigmaCore M ⊓ centralizer (A : Set G) = ⊥ :=
    (h₂ G hG M A p hM hp hpσM hAM hplane).2.1
  have hSN : sigmaCore M ⊓ normalizer (A : Set G) = ⊥ :=
    inf_normalizer_eq_bot_of_inf_centralizer_eq_bot (le_normalizer_sigmaCore M) hAM
      (fun _ hy _ hz => hplane.isElementaryAbelian.mul_comm hy hz) hSC
  exact hx1 (mem_bot.1 (hSN ▸ mem_inf.2 ⟨hxS, hnorm hxJ⟩))

theorem FTS_complement_plane_primes_in_opposite_core
    (_h₁ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₂ : Statements.FTS_outside_sigma_plane_structure.{u})
    (_h₃ : Statements.FTS_plane_maximal_overgroups.{u}) :
    Statements.FTS_complement_plane_primes_in_opposite_core.{u} := by
  intro G _ _ hG M hM T hT _hMT hsemi hx p hpτ
  obtain ⟨x, hxmem, hx1⟩ := hx
  obtain ⟨hxS, hxJ⟩ := mem_inf.1 hxmem
  exact mem_sigmaPrimes_of_mem_tauTwoPrimes_of_mem_sigmaCore_inf h₂ G
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable⟩
    (mem_maximalSubgroups.1 hM) (mem_maximalSubgroups.1 hT) hsemi hxS hxJ hx1 hpτ

end

end CFSG.FeitThompson.Proofs
