module

public import Mathlib
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.KappaGlobalPairExhaustion
import CFSG.FeitThompson.Local.KappaFixedCoreMeetsNoConjugateMaximal
import CFSG.FeitThompson.Local.KappaResidualComplementNormalizerEscape
import CFSG.FeitThompson.Local.KappaNonemptyNoPrimeInOtherSigma
import CFSG.FeitThompson.Local.KappaResidualInPrescribedComplement
import CFSG.FeitThompson.Local.FiniteNilpotentSubnormal
import CFSG.FeitThompson.Local.PrimeActionChiefFactorsBelowFitting
import CFSG.FeitThompson.Local.FittingSplitsNormalHall
import CFSG.FeitThompson.Local.SubnormalOvergroupOutsideConjugate
import CFSG.FeitThompson.Local.QuotientFittingInvariantComplement
import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
import CFSG.FeitThompson.Foundations.NormalNilpotentInFitting
import CFSG.FeitThompson.Foundations.PiSubgroupInHallSolvable
import CFSG.FeitThompson.Representations.NoInducedIrreducibleFixedOrbitOrder
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
open CFSG.FeitThompson.FreeCore
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep03

universe u

variable {G : Type*} [Group G]

theorem exists_isInternalSemidirectProduct_sigmaCore_ge_of_isHallPiSubgroupOf [Finite G]
    {H K : Subgroup G}
    (hHall : IsHallPiSubgroupOf (sigmaPrimes H) (sigmaCore H) H)
    (hsolv : Group.IsSolvable ↥H) (hKH : K ≤ H)
    (hKσ : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥K → p ∉ sigmaPrimes H) :
    ∃ D : Subgroup G, D ≤ H ∧ IsInternalSemidirectProduct H (sigmaCore H) D ∧ K ≤ D := by
  have := hsolv
  have hcard : Nat.card ↥(K.subgroupOf H) = Nat.card ↥K :=
    Nat.card_congr (subgroupOfEquivOfLe hKH).toEquiv
  have hpi : IsPiSubgroup ((sigmaPrimes H)ᶜ) (K.subgroupOf H) := by
    refine isPiSubgroup_iff.2 fun p hp => ?_
    rw [hcard] at hp
    exact hKσ p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  obtain ⟨D₀, hD₀, hKD₀⟩ := exists_isHallSubgroup_ge_of_isPiSubgroup (G := ↥H) hpi
  have hDsub : ((D₀.map H.subtype).subgroupOf H) = D₀ := by
    rw [Subgroup.subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]
  refine ⟨D₀.map H.subtype, map_subtype_le _, ?_, ?_⟩
  · have hV : IsHallSubgroup (sigmaPrimes H) ((sigmaCore H).subgroupOf H) :=
      isHallSubgroup_iff_isHallPiSubgroup.2 hHall.2
    have hK' : IsHallSubgroup ((sigmaPrimes H)ᶜ) ((D₀.map H.subtype).subgroupOf H) := by
      rw [hDsub]; exact hD₀
    obtain ⟨hsup, hinf⟩ := sup_eq_and_inf_eq_bot_of_isHallSubgroup_compl
      (sigmaCore_le H) (map_subtype_le _) hV hK'
      ((map_subtype_le _).trans (le_normalizer_sigmaCore H))
    exact ⟨hsup, le_normalizer_sigmaCore H, disjoint_iff.2 hinf⟩
  · have h := Subgroup.map_mono (f := H.subtype) hKD₀
    rwa [map_subgroupOf_eq_of_le hKH] at h

theorem isSubnormal_subgroupOf_of_le_fittingOfNormal [Finite G] {K D : Subgroup G}
    (hKF : K ≤ fittingOfNormal D) : (K.subgroupOf D).IsSubnormal := by
  have h1 : K.subgroupOf D ≤ fittingRaw ↥D := by
    rw [← subgroupOf_fittingOfNormal D]; exact comap_mono hKF
  have : Group.IsNilpotent ↥(fittingRaw ↥D) := isNilpotent_of_le_fittingRaw le_rfl
  exact Subgroup.IsSubnormal.trans h1 (isSubnormal_of_finite_of_isNilpotent _)
    (fittingRaw_normal ↥D).isSubnormal

theorem FTS_kappa_residual_containing_complement_fitting
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_local_pair.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_free_nonfitting_prime_alternative.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_prime_overgroup_position.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_containing_complement_fitting.{u} := by
  have hexh := FNI_kappa_global_pair_exhaustion h₁ h₂ h₃ h₆
  have hdisjK := FTS_kappa_fixed_core_outside_conjugate_disjoint h₁ h₃ h₆
  intro G _ _ hG r M K U A Mstar R H hP
  have : Fintype G := Fintype.ofFinite G
  have hamb : Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hG02 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hG08 : Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable⟩
  have hsetup08 : Prep08.IsKappaResidualSetup M K U A Mstar R H r :=
    { isCoatom_M := hP.config.isCoatom
      kappa_nonempty := hP.config.kappaPrimes_nonempty
      isHall_K := ⟨hP.config.isHallKappa.1, hP.config.isHallKappa.2⟩
      isHall_U := ⟨hP.config.isHallCompl.1, hP.config.isHallCompl.2⟩
      semidirect_M := hP.config.isInternalSemidirectProduct
      semidirect_UK := hP.config.isInternalSemidirectProduct_complement
      isMulCommutative_U := hP.isMulCommutative_U
      centralizer_U := hP.centralizer_eq_bot
      U_ne_bot := hP.U_ne_bot
      A_eq := hP.A_eq
      isCoatom_Mstar := hP.isCoatom_Mstar
      exists_prime_order_le_K := hP.exists_prime_order_normalizer_le
      prime_r := hP.prime_r
      r_dvd := hP.dvd_natCard_U
      isSylow_R := (Prep08.isSylowOf_iff_natCard hP.prime_r hP.isSylowSubgroupOf_R.le).2
        hP.isSylowSubgroupOf_R.2
      isCoatom_H := hP.isCoatom_H
      normalizer_R_le := hP.normalizer_R_le }
  obtain ⟨hKprime, hUKH, -, -, hkappaH, hKsigmaH⟩ := h₅ G hG08 M K U A Mstar R H r hsetup08
  set q : ℕ := Nat.card ↥K with hq
  have hKsetup : Prep03.IsKappaSetup G M K A (K ⊔ A) :=
    { ambient := hamb
      isCoatom := hP.config.isCoatom
      kappa_nonempty := hP.config.kappaPrimes_nonempty
      isHall_K := isHallPiOf_of_isHallPiSubgroupOf hP.config.isHallKappa
      A_eq := hP.A_eq
      Z_eq := rfl }
  obtain ⟨Ms, ⟨hMsCo, hMsEx⟩, hMsUniq, -, hAne, hAhall, hcentK, -, -, -, -, hKcl, -, -, -⟩ :=
    h₂ G M K A (K ⊔ A) hKsetup
  have hMsEqStar : Mstar = Ms :=
    hMsUniq Mstar hP.isCoatom_Mstar hP.exists_prime_order_normalizer_le
  subst hMsEqStar
  have hcentK' : sigmaCore Mstar ⊓ centralizer (A : Set G) = K := hcentK
  have hKSMs : K ≤ sigmaCore Mstar := by rw [← hcentK']; exact inf_le_left
  have hqσ : q ∈ sigmaPrimes Mstar :=
    isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore Mstar) q (Nat.mem_primeFactors.2
      ⟨hKprime, Subgroup.card_dvd_of_le hKSMs, Nat.card_pos.ne'⟩)
  have hKH : K ≤ H := le_sup_right.trans hUKH
  have hHsolv : Group.IsSolvable ↥H := hG.isSolvable H hP.isCoatom_H.1
  have hSHall : IsHallPiSubgroupOf (sigmaPrimes H) (sigmaCore H) H :=
    (h₁ G hG02 H hP.isCoatom_H).1
  obtain ⟨p, hpU⟩ : ∃ p : ℕ, p ∈ (Nat.card ↥U).primeFactors := by
    have hne : Nat.card ↥U ≠ 1 := fun h => hP.U_ne_bot (Subgroup.card_eq_one.1 h)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    exact ⟨p, Nat.mem_primeFactors.2 ⟨hp, hpd, Nat.card_pos.ne'⟩⟩
  have hpmem := isPiSubgroup_iff.1 hP.config.isHallCompl.isPiSubgroup p hpU
  have hpdvdM : p ∣ Nat.card ↥M :=
    (Nat.dvd_of_mem_primeFactors hpU).trans (Subgroup.card_dvd_of_le hP.config.isHallCompl.le)
  refine ⟨exists_isInternalSemidirectProduct_sigmaCore_ge_of_isHallPiSubgroupOf
      hSHall hHsolv hKH hKsigmaH,
    fun D hDH hsemi hKD => ?_⟩
  have hKF : K ≤ fittingOfNormal D := by
    by_contra hKF
    have hcfg : IsKappaFreeNonfittingConfig q H D K :=
      { isCoatom := hP.isCoatom_H
        kappaPrimes_eq_empty := hkappaH
        le_of_E := hDH
        isInternalSemidirectProduct := hsemi
        prime := hKprime
        le_of_Q := hKD
        natCard_Q := rfl
        not_le_fitting := hKF }
    obtain ⟨T, hTco, hT⟩ := h₄ G hG q H D K hcfg
    rcases hT with ⟨hqτ, -, huniq⟩ | ⟨hqκ, hKT, hTsemi⟩
    ·
      have hTeq : T = Mstar := (hKcl K le_rfl hKprime).2.2.2 T huniq.isCoatom huniq.le
      rw [hTeq] at hqτ
      exact notMem_sigmaPrimes_of_mem_tauTwoPrimes hqτ hqσ
    ·
      obtain ⟨g, hg⟩ := hexh G M K A (K ⊔ A) Mstar hKsetup hP.isCoatom_Mstar
        hP.exists_prime_order_normalizer_le hMsUniq T hTco ⟨q, hqκ⟩
      rcases hg with hgM | hgMs
      ·
        have hTsolv : Group.IsSolvable ↥T := hG.isSolvable T hTco.1
        obtain ⟨L, hL, -⟩ :=
          exists_isHallPiSubgroupOf_ge (π := kappaPrimes T) (M := T) (Q := ⊥) hTsolv bot_le
            (isPiSubgroup_iff.2 (by simp))
        have hcardT : Nat.card ↥T = Nat.card ↥(sigmaCore T) * Nat.card ↥L :=
          (hTsemi L hL).natCard_eq_mul
        have hMT : Nat.card ↥M = Nat.card ↥T := by rw [← hgM, natCard_conjSub]
        have hσeq : sigmaPrimes T = sigmaPrimes M := by rw [← hgM, sigmaPrimes_conjSub]
        have hκeq : kappaPrimes T = kappaPrimes M := by rw [← hgM, kappaPrimes_conjSub]
        have hpdvdT : p ∣ Nat.card ↥(sigmaCore T) * Nat.card ↥L := by
          rw [← hcardT, ← hMT]; exact hpdvdM
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpU
        rcases (Nat.Prime.dvd_mul hpp).1 hpdvdT with hd | hd
        · refine hpmem.2.1 ?_
          rw [← hσeq]
          exact isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore T) p
            (Nat.mem_primeFactors.2 ⟨hpp, hd, Nat.card_pos.ne'⟩)
        · refine hpmem.2.2 ?_
          rw [← hκeq]
          exact isPiSubgroup_iff.1 hL.isPiSubgroup p
            (Nat.mem_primeFactors.2 ⟨hpp, hd, Nat.card_pos.ne'⟩)
      ·
        have hκ : q ∈ kappaPrimes Mstar := by rw [← hgMs, kappaPrimes_conjSub]; exact hqκ
        exact Set.disjoint_left.1 (disjoint_kappaPrimes_sigmaPrimes Mstar) hκ hqσ
  refine ⟨hKF, ?_⟩
  have hKbot : K ≠ ⊥ := fun h => hKprime.one_lt.ne' (by rw [hq, h]; simp)
  have hκMs : (kappaPrimes Mstar).Nonempty := by
    obtain ⟨s, hs⟩ : ∃ s : ℕ, s ∈ (Nat.card ↥A).primeFactors := by
      have hne : Nat.card ↥A ≠ 1 := fun h => hAne (Subgroup.card_eq_one.1 h)
      obtain ⟨s, hsp, hsd⟩ := Nat.exists_prime_and_dvd hne
      exact ⟨s, Nat.mem_primeFactors.2 ⟨hsp, hsd, Nat.card_pos.ne'⟩⟩
    exact ⟨s, hAhall.2.1 s hs⟩
  have hAhall' : IsHallPiSubgroupOf (kappaPrimes Mstar) A Mstar :=
    isHallPiSubgroupOf_of_isHallPiOf hAhall fun _ _ => Iff.rfl
  refine le_of_isSubnormal_of_inf_conj_eq_bot hKbot (hKSMs.trans (sigmaCore_le Mstar))
    (fun g hg => ?_) hKD (isSubnormal_subgroupOf_of_le_fittingOfNormal hKF)
  have hd := hdisjK G hG Mstar hP.isCoatom_Mstar hκMs A hAhall' g hg
  rw [hcentK'] at hd
  exact hd

end

end CFSG.FeitThompson.Proofs
