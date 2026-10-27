module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.AuxiliaryOppositeTauTwoRankOne
import CFSG.FeitThompson.Local.UniquenessTransferCentralizerRankTwo
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
import CFSG.FeitThompson.Foundations.NilpotentHomImageNilpotent
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

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G] [Finite G]

theorem eq_natCard_of_mem_tauTwoPrimes
    (h₂ : Statements.FTS_kappa_residual_prime_overgroup_position.{u})
    (h₃ : Statements.FTS_residual_rank_two_plane_partner_fitting.{u})
    (hG : Prep08.IsMinimalSimpleOddOrder G)
    {M K U A Mstar R H : Subgroup G} {r : ℕ}
    (hsetup : Prep08.IsKappaResidualSetup M K U A Mstar R H r)
    (hne : (tauTwoPrimes H).Nonempty) {p : ℕ} (hp : p ∈ tauTwoPrimes H) :
    p = Nat.card ↥K := by
  obtain ⟨hq, -, -, hHMstar, -, -⟩ := h₂ G hG M K U A Mstar R H r hsetup
  obtain ⟨hmain, hexists⟩ := h₃ G hG M K U A Mstar R H r hsetup hne
  obtain ⟨B, hBle, hBplane⟩ := hexists p hp
  obtain ⟨-, -, -, hBF, hQsylow, -, hQuniq⟩ := hmain p hp B hBle hBplane
  by_contra hpq
  have hpp : p.Prime := prime_of_mem_tauTwoPrimes hp
  set q := Nat.card ↥K with hqdef
  obtain ⟨X, hXK, hXprime, hXMstar⟩ := hsetup.exists_prime_order_le_K
  have hXq : Nat.card ↥X = q :=
    (Nat.prime_dvd_prime_iff_eq hXprime hq).1 (Subgroup.card_dvd_of_le hXK)
  have hqdvd : q ∣ Nat.card ↥Mstar :=
    hXq ▸ Subgroup.card_dvd_of_le (le_trans Subgroup.le_normalizer hXMstar)
  set Q := Prep08.pCoreOfSubgroup q Mstar with hQdef
  have hQcard : Nat.card ↥Q = q ^ (Nat.card ↥Mstar).factorization q :=
    (Prep08.isSylowOf_iff_natCard hq (Prep08.pCoreOfSubgroup_le q Mstar)).1 hQsylow
  have hfpos : 0 < (Nat.card ↥Mstar).factorization q :=
    hq.factorization_pos_of_dvd Nat.card_pos.ne' hqdvd
  have hqdvdQ : q ∣ Nat.card ↥Q := hQcard ▸ dvd_pow_self q hfpos.ne'
  have hQbot : ⊥ < Q := by
    refine bot_lt_iff_ne_bot.2 fun h => ?_
    rw [h, Subgroup.card_bot] at hqdvdQ
    exact hq.ne_one (Nat.dvd_one.1 hqdvdQ)
  have hFeq : Prep08.fittingOf Mstar = (fittingRaw ↥Mstar).map Mstar.subtype := rfl
  have hFnil : Group.IsNilpotent ↥(Prep08.fittingOf Mstar) := by
    rw [hFeq]; exact isNilpotent_map Mstar.subtype (fittingRaw ↥Mstar)
  have hQF : Q ≤ Prep08.fittingOf Mstar := by
    rw [hQdef, hFeq, Prep08.pCoreOfSubgroup]
    exact Subgroup.map_mono (pCore_le_fittingRaw hq)
  have hcop : (Nat.card ↥B).Coprime (Nat.card ↥Q) := by
    rw [hBplane.natCard, hQcard]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hpp hq).2 hpq)
  have hBC : B ≤ centralizer ((Q : Subgroup G) : Set G) :=
    le_centralizer_of_coprime_natCard_of_isNilpotent (Prep08.fittingOf Mstar) hFnil hBF hQF hcop
  have hrank : 2 ≤ elementaryAbelianPRank p ↥B :=
    (Prep08.IsPlaneAt.elementaryAbelianPRank_eq hpp hBplane).ge
  have := hG.isSimpleGroup
  have hBuniq : IsUniqueMaximalOvergroup B Mstar :=
    isUniqueMaximalOvergroup_of_le_centralizer hpp hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hQbot hQuniq hBC hrank
  have hHeq : H = Mstar := hBuniq.eq_of_isCoatom hsetup.isCoatom_H (le_trans hBle inf_le_left)
  exact hHMstar 1 (by simpa using hHeq)

theorem FTS_residual_normalizer_single_rank_two_prime
    (h₁ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₂ : Statements.FTS_kappa_residual_prime_overgroup_position.{u})
    (h₃ : Statements.FTS_residual_rank_two_plane_partner_fitting.{u}) :
    Statements.FTS_residual_normalizer_single_rank_two_prime.{u} := by
  intro G _ _ hG M K U A Mstar R H r hsetup hne
  have hq : (Nat.card ↥K).Prime := (h₂ G hG M K U A Mstar R H r hsetup).1
  have hG' : IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have := hG.isSimpleGroup
  have hsingle : tauTwoPrimes H = {Nat.card ↥K} := by
    obtain ⟨p, hp⟩ := hne
    refine Set.eq_singleton_iff_unique_mem.2
      ⟨(eq_natCard_of_mem_tauTwoPrimes h₂ h₃ hG hsetup ⟨p, hp⟩ hp) ▸ hp, fun x hx => ?_⟩
    exact eq_natCard_of_mem_tauTwoPrimes h₂ h₃ hG hsetup ⟨p, hp⟩ hx
  have hmem : Nat.card ↥K ∈ tauTwoPrimes H := by rw [hsingle]; rfl
  have hβG : Nat.card ↥K ∉ betaPrimes G :=
    notMem_betaPrimes_of_mem_tauTwoPrimes h₁ hG' hsetup.isCoatom_H hmem
  refine ⟨hq, hsingle, hβG, fun hmemβ => hβG ?_⟩
  rw [betaPrimes_subgroup_eq_sigmaPrimes_inter hG.not_isMulCommutative hG.odd_natCard
    hG.isSolvable_of_ne_top hsetup.isCoatom_Mstar] at hmemβ
  exact hmemβ.2

end

end CFSG.FeitThompson.Proofs
