module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
import CFSG.FeitThompson.Local.TauThreeHallFixedCentralizer
import CFSG.FeitThompson.Local.BetaCoreHallQuotient
import CFSG.FeitThompson.Local.DerivedComplementCentralizesBetaPrimeHall
import CFSG.FeitThompson.Local.SigmaHallCentralizerExcludesKappa
import CFSG.FeitThompson.Local.KappaFixedPrimeCentralizerSylowUnique
import CFSG.FeitThompson.Local.FixedLineCharacteristicChainPrimeFactors
import CFSG.FeitThompson.Local.BetaSubgroupNormalizerInMaximal
import CFSG.FeitThompson.Local.BetaPrimesSigmaCompatibility
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.InvariantHallPiSubgroupExtension
import CFSG.FeitThompson.OddOrder.SigmaHallSubgroupNormalizer
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
import CFSG.FeitThompson.Definitions.AlphaCore

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson

universe u

variable {G : Type u} [Group G]

theorem inf_centralizer_le_centralizer_sup {A P Q : Subgroup G}
    (hQ : A ≤ centralizer (Q : Set G)) :
    A ⊓ centralizer (P : Set G) ≤ centralizer ((P ⊔ Q : Subgroup G) : Set G) := by
  rw [le_centralizer_iff]
  exact sup_le (le_centralizer_iff.1 inf_le_right) (le_centralizer_iff.1 (inf_le_left.trans hQ))

variable [Finite G]

theorem factorization_natCard_eq_of_not_dvd_relIndex {u : ℕ} {H C S : Subgroup G}
    (hHC : H ≤ C) (hCS : C ≤ S) (hnd : ¬ u ∣ H.relIndex S) :
    (Nat.card C).factorization u = (Nat.card S).factorization u := by
  have hHS : H ≤ S := hHC.trans hCS
  have hne : H.relIndex S ≠ 0 := by
    rw [← index_subgroupOf]; exact Subgroup.index_ne_zero_of_finite
  have hmul : H.relIndex S * Nat.card H = Nat.card S := relIndex_mul_natCard hHS
  have hSH : (Nat.card S).factorization u = (Nat.card H).factorization u := by
    rw [← hmul, Nat.factorization_mul hne Nat.card_pos.ne']
    simp [Nat.factorization_eq_zero_of_not_dvd hnd]
  have h1 : (Nat.card H).factorization u ≤ (Nat.card C).factorization u :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
      (Subgroup.card_dvd_of_le hHC) u
  have h2 : (Nat.card C).factorization u ≤ (Nat.card S).factorization u :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
      (Subgroup.card_dvd_of_le hCS) u
  omega

theorem not_dvd_relIndex_of_natCard_eq_pow {u : ℕ} {U S : Subgroup G} (hu : u.Prime)
    (hUS : U ≤ S) (hUcard : Nat.card U = u ^ (Nat.card S).factorization u) :
    ¬ u ∣ U.relIndex S := by
  intro hdvd
  have hne : U.relIndex S ≠ 0 := by
    rw [← index_subgroupOf]; exact Subgroup.index_ne_zero_of_finite
  have hmul : U.relIndex S * Nat.card U = Nat.card (S : Subgroup G) := relIndex_mul_natCard hUS
  have hfac : (Nat.card (S : Subgroup G)).factorization u =
      (U.relIndex S).factorization u + (Nat.card U).factorization u := by
    rw [← hmul, Nat.factorization_mul hne Nat.card_pos.ne']; simp
  rw [hUcard, Nat.Prime.factorization_pow hu] at hfac
  have hpos : 0 < (U.relIndex S).factorization u := hu.factorization_pos_of_dvd hne hdvd
  simp at hfac
  omega

theorem FNI_tau13_core_fixed_sylow_regular_normalizer
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_fixed_line_centralizer_unique.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_three_prime_normalizer_transfer.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_tau13_core_fixed_sylow_regular_normalizer.{u} := by
  intro G _ _ hG M E E₁ E₂ E₃ hME hsplit p q P Q hp hPE₁ hPcard hq hQsyl hQne hQP hαβ hAC
    L hL hLnc hEL hNQL u U hu huC hUsyl hEU
  have hMc : IsCoatom M := hME.isCoatom
  have := hG.isSimpleGroup
  have hG2 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG6 : Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG7 : CFSG.FeitThompson.IsFTAmbient G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hG9 : CFSG.FeitThompson.Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨hHallOf, hHallG, hSM⟩ :=
    letI : Fintype G := Fintype.ofFinite G
    h₁ G hG2 M hMc
  have hHallM : IsHallPiSubgroup (sigmaPrimes M) ((sigmaCore M).subgroupOf M) := hHallOf.2
  have hEM : E ≤ M := hME.le
  have hE₃E : E₃ ≤ E := hsplit.le_E₃
  have hQE₃ : Q ≤ E₃ := hQsyl.le
  have hCeq : sigmaCore M ⊓ centralizer (Q : Set G) =
      sigmaCore M ⊓ centralizer (E₃ : Set G) :=
    FNI_tau_three_hall_fixed_centralizer h₄ G hG M E E₁ E₂ E₃ hME hsplit Q hQE₃ hQne
  have hUC : U ≤ sigmaCore M ⊓ centralizer (E₃ : Set G) := hUsyl.le
  have hUS : U ≤ sigmaCore M := hUC.trans inf_le_left
  have hUcentQ : U ≤ centralizer (Q : Set G) :=
    (hUC.trans inf_le_right).trans (centralizer_le (SetLike.coe_subset_coe.2 hQE₃))
  have hUM : U ≤ M := hUS.trans (sigmaCore_le M)
  have hUL : U ≤ L := hUcentQ.trans ((centralizer_le_normalizer _).trans hNQL)
  have hUcardC : Nat.card U =
      u ^ (Nat.card ↥(sigmaCore M ⊓ centralizer (E₃ : Set G) : Subgroup G)).factorization u :=
    (_root_.CFSG.FeitThompson.isSylowIn_iff_natCard hu hUsyl.le).1 hUsyl
  have hudvdU : u ∣ Nat.card U := by
    rw [hUcardC]
    exact dvd_pow_self u (hu.factorization_pos_of_dvd Nat.card_pos.ne' huC).ne'
  have hUne : U ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hudvdU
    exact hu.one_lt.ne' (Nat.eq_one_of_dvd_one hudvdU)
  have hpp : p.Prime := prime_of_mem_tau1Primes hp
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPcard
    exact hpp.one_lt.ne' hPcard.symm
  by_cases huβ : u ∈ betaPrimes ↥M
  ·
    have hUβ : IsPiSubgroup (betaPrimes ↥M) U := isPiSubgroup_of_natCard_eq_pow hu hUcardC huβ
    have hB := isHallPiIn_betaCore h₂ hG6 hMc hHallM hSM
    have hBHall : IsHallPiSubgroup (betaPrimes ↥M) ((betaCore M).subgroupOf M) := by
      constructor
      · refine isPiSubgroup_iff.2 fun r hr => hB.2.1 r ?_
        rwa [natCard_subgroupOf (betaCore_le M)] at hr
      · intro r hr
        rw [index_subgroupOf] at hr
        exact hB.2.2 r hr
    have hAB : _root_.CFSG.FeitThompson.alphaCoreIn M = betaCore M := by
      rw [_root_.CFSG.FeitThompson.alphaCoreIn_eq, betaCore_eq_map_piCore, alphaCore_eq_piCore, hαβ]
    refine ⟨normalizer_le_of_isPiSubgroup_betaPrimes hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hMc hUM hUne hUβ, ?_⟩
    have hUA : U ≤ _root_.CFSG.FeitThompson.alphaCoreIn M := by
      rw [hAB]
      exact le_of_isHallPiSubgroup_subgroupOf (betaCore_le M) (le_normalizer_betaCore M)
        hBHall hUM hUβ
    refine le_bot_iff.1 ?_
    rw [← hAC]
    exact le_inf (inf_le_left.trans hUA) (inf_centralizer_le_centralizer_sup hUcentQ)
  ·
    obtain ⟨H, hHHall, hHcent⟩ := FTS_derived_complement_centralizes_beta_prime_hall h₁ h₂ G hG7
      M hMc E hEM hME.isInternalSemidirectProduct
    have hπ : u ∈ {r : ℕ | r.Prime ∧ r ∉ betaPrimes ↥M} := ⟨hu, huβ⟩
    have hHS : H ≤ sigmaCore M := hHHall.1
    have hHQ : H ≤ centralizer (Q : Set G) :=
      (le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hHcent)).trans
        (centralizer_le (SetLike.coe_subset_coe.2 (hQE₃.trans hsplit.le_commutator_E₃)))
    have hHC : H ≤ sigmaCore M ⊓ centralizer (E₃ : Set G) := by
      rw [← hCeq]; exact le_inf hHS hHQ
    have hnd : ¬ u ∣ H.relIndex (sigmaCore M) := by
      intro hdvd
      refine hHHall.2.notMem_of_mem_primeFactors_index u ?_ hπ
      rw [index_subgroupOf]
      exact Nat.mem_primeFactors.2 ⟨hu, hdvd, by
        rw [← index_subgroupOf]; exact Subgroup.index_ne_zero_of_finite⟩
    have hUfull : Nat.card U = u ^ (Nat.card ↥(sigmaCore M)).factorization u := by
      rw [hUcardC, factorization_natCard_eq_of_not_dvd_relIndex hHC inf_le_left hnd]
    have huσ : u ∈ sigmaPrimes M := isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) u
      (Nat.mem_primeFactors.2
        ⟨hu, hudvdU.trans (Subgroup.card_dvd_of_le hUS), Nat.card_pos.ne'⟩)
    have hndM : ¬ u ∣ U.relIndex M := by
      intro hdvd
      have hmul := Subgroup.relIndex_mul_relIndex U (sigmaCore M) M hUS (sigmaCore_le M)
      rcases (Nat.Prime.dvd_mul hu).1 (hmul ▸ hdvd) with h | h
      · exact not_dvd_relIndex_of_natCard_eq_pow hu hUS hUfull h
      · refine hHallM.notMem_of_mem_primeFactors_index u ?_ huσ
        rw [index_subgroupOf]
        exact Nat.mem_primeFactors.2 ⟨hu, h, by
          rw [← index_subgroupOf]; exact Subgroup.index_ne_zero_of_finite⟩
    have hcop : Nat.Coprime (Nat.card U) (U.relIndex M) := by
      rw [hUfull]
      exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hu).2 hndM)
    refine ⟨normalizer_le_of_le_sigmaCore hUne hUS hcop, ?_⟩
    by_contra hCU
    have hdvdcard : Nat.card ↥(U ⊓ centralizer (P : Set G) : Subgroup G) ∣
        u ^ (Nat.card ↥(sigmaCore M)).factorization u :=
      hUfull ▸ Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow hu).1 hdvdcard
    have hjpos : j ≠ 0 := by
      intro h
      rw [h, pow_zero] at hjeq
      exact hCU (Subgroup.card_eq_one.1 hjeq)
    have hudvd : u ∣ Nat.card ↥(U ⊓ centralizer (P : Set G) : Subgroup G) := by
      rw [hjeq]; exact dvd_pow_self u hjpos
    obtain ⟨x, hx, hxord⟩ := exists_mem_orderOf_eq_of_dvd hu hudvd
    have hXcard : Nat.card (zpowers x) = u := by rw [Nat.card_zpowers, hxord]
    have hXle : zpowers x ≤ U ⊓ centralizer (P : Set G) := zpowers_le.2 hx
    have hXcent : zpowers x ≤
        CFSG.FeitThompson.Prep09.centIn (sigmaCore M) (P : Set G) := by
      rw [CFSG.FeitThompson.Prep09.centIn_def]
      exact le_inf ((hXle.trans inf_le_left).trans hUS) (hXle.trans inf_le_right)
    obtain ⟨-, hsyl⟩ := h₃ G hG9 M hMc E hEM hME.isInternalSemidirectProduct E₁ hsplit.le_E₁
      hsplit.isHall_E₁ P hPE₁ hPne u hu (zpowers x) hXcent hXcard
    have : Fact u.Prime := ⟨hu⟩
    have hcardsub : Nat.card ↥(U.subgroupOf (sigmaCore M)) =
        u ^ (Nat.card ↥(sigmaCore M)).factorization u := by
      rw [natCard_subgroupOf hUS, hUfull]
    have huniq := hsyl (Sylow.ofCard (U.subgroupOf (sigmaCore M)) hcardsub)
    rw [Sylow.coe_ofCard, Subgroup.map_subgroupOf_eq_of_le hUS] at huniq
    exact hLnc 1 (by rw [_root_.CFSG.FeitThompson.conjSubgroup_one]
                     exact (huniq.eq_of_isCoatom hL hUL).symm)

end

end CFSG.FeitThompson.Proofs
