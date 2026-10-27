module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.CommonPrimeFixedCoreFittingEnvelope
import CFSG.FeitThompson.Local.KappaFixedPrimeCentralizerSylowUnique
import CFSG.FeitThompson.Local.SigmaComplementAbelianNilpotent
import CFSG.FeitThompson.Local.AbelianHallTauTwoControlsCentralizers
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerCommonFactor
import CFSG.FeitThompson.Local.NonabelianAmbientPlaneCentralizer
import CFSG.FeitThompson.Local.SigmaConjugateIntersectionCyclic
import CFSG.FeitThompson.Local.HallKappaSubgroupTI
import CFSG.FeitThompson.Local.KappaResidualRankTwoExclusion
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting
import CFSG.FeitThompson.Local.FittingFixedFreeDisplacementInFitting
import CFSG.FeitThompson.Local.QuotientFittingInvariantComplement
import CFSG.FeitThompson.Local.FittingSplitsNormalHall
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Foundations.PiSubgroupInHallSolvable
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

variable {G : Type*} [Group G]

theorem commutator_eq_bot_of_le_of_isMulCommutative {F X Y : Subgroup G}
    (hF : IsMulCommutative ↥F) (hX : X ≤ F) (hY : Y ≤ F) : ⁅X, Y⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  exact congrArg Subtype.val (hF.is_comm.comm (⟨y, hY hy⟩ : ↥F) ⟨x, hX hx⟩)

theorem fittingOf_eq_fittingOfNormal [Finite G] (M : Subgroup G) :
    Prep08.fittingOf M = fittingOfNormal M := map_fittingRaw_subtype_eq_fittingOfNormal M

theorem FTS_residual_rank_two_plane_partner_fitting
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_local_pair.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_partner_intersection_complement.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_prime_overgroup_position.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_residual_rank_two_plane_partner_fitting.{u} := by
  intro G _ _ hG M K U A Mstar R H r hs _hne
  have hsimple := hG.isSimpleGroup
  have : Fintype G := Fintype.ofFinite G
  have hFT : IsFTAmbient G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hG04 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG02 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hamb : Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨hqprime, -, -, -, -, -⟩ := h₈ G hG M K U A Mstar R H r hs
  obtain ⟨hHsplit, hKF⟩ :=
    h₇ G hFT r M K U A Mstar R H (isKappaResidualPartner_of_isKappaResidualSetup hs)
  obtain ⟨hSH, -, -⟩ := h₂ G hG02 H hs.isCoatom_H
  obtain ⟨hSMs, -, -⟩ := h₂ G hG02 Mstar hs.isCoatom_Mstar
  have hDle : H ⊓ Mstar ≤ H := inf_le_left
  have hDπ : ∀ s : ℕ, s.Prime → s ∣ Nat.card ↥(H ⊓ Mstar) → s ∉ sigmaPrimes H := fun s hsp hsd =>
    notMem_sigmaPrimes_of_dvd_natCard_complement hSH.2 hHsplit hsp hsd
  have hFDle : fittingOfNormal (H ⊓ Mstar) ≤ H ⊓ Mstar := fittingOfNormal_le _
  have hFDnil : Group.IsNilpotent ↥(fittingOfNormal (H ⊓ Mstar)) := by
    rw [← map_fittingRaw_subtype_eq_fittingOfNormal]
    exact isNilpotent_map_fittingRaw _
  have hFDab : IsMulCommutative ↥(fittingOfNormal (H ⊓ Mstar)) := by
    refine (FBG_sigma_complement_abelian_nilpotent h₂ h₆ G hG02 H hs.isCoatom_H).1
      (fittingOfNormal (H ⊓ Mstar)) (hFDle.trans hDle) hFDnil (isPiSubgroup_iff.2 fun s hs' => ?_)
    exact hDπ s (Nat.prime_of_mem_primeFactors hs')
      ((Nat.dvd_of_mem_primeFactors hs').trans (Subgroup.card_dvd_of_le hFDle))
  have hsetup03 : Prep03.IsKappaSetup G M K A (K ⊔ A) :=
    { ambient := hamb
      isCoatom := hs.isCoatom_M
      kappa_nonempty := hs.kappa_nonempty
      isHall_K := isHallPiOf_of_isHallPiSubgroupOf ⟨hs.isHall_K.1, hs.isHall_K.2⟩
      A_eq := hs.A_eq
      Z_eq := rfl }
  obtain ⟨Mstar₀, -, huniq, -, hAne, hAHall₀, hKeq₀, -⟩ := h₃ G M K A (K ⊔ A) hsetup03
  have hMs : Mstar = Mstar₀ := huniq Mstar hs.isCoatom_Mstar hs.exists_prime_order_le_K
  rw [← hMs] at hAHall₀ hKeq₀
  have hKeq : sigmaCore Mstar ⊓ centralizer (A : Set G) = K := hKeq₀
  have hAHall : IsHallPiSubgroupOf (kappaPrimes Mstar) A Mstar :=
    ⟨hAHall₀.1, isHallPiSubgroup_subgroupOf_of_isHallPiOf hAHall₀⟩
  obtain ⟨s, hsp, hsdvd⟩ := Nat.exists_prime_and_dvd (n := Nat.card ↥A)
    (fun h => hAne (Subgroup.card_eq_one.1 h))
  have hκMs : (kappaPrimes Mstar).Nonempty :=
    ⟨s, hAHall₀.2.1 s (Nat.mem_primeFactors.2 ⟨hsp, hsdvd, Nat.card_pos.ne'⟩)⟩
  have hKS : K ≤ sigmaCore Mstar := by rw [← hKeq]; exact inf_le_left
  have hKbot : K ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hqprime
    exact Nat.not_prime_one hqprime
  have hKpg : IsPGroup (Nat.card ↥K) ↥K := IsPGroup.of_card (n := 1) (by rw [pow_one])
  have hqσMs : Nat.card ↥K ∈ sigmaPrimes Mstar :=
    mem_sigmaPrimes_of_isPGroup_le_sigmaCore hqprime hKbot hKpg hKS
  have hZcard : Nat.card ↥(sigmaCore Mstar ⊓ centralizer (A : Set G)) = Nat.card ↥K := by
    rw [hKeq]
  obtain ⟨hQnormal, hQsylow, hCF, -⟩ :=
    FTS_common_prime_fixed_core_fitting_envelope h₁ h₄ G hFT Mstar
      (mem_maximalSubgroups.2 hs.isCoatom_Mstar) hκMs A hAHall (Nat.card ↥K) hqprime hZcard
  rw [hKeq] at hCF
  have hsetupMs : Prep03.IsKappaSetup G Mstar A K (A ⊔ K) :=
    { ambient := hamb
      isCoatom := hs.isCoatom_Mstar
      kappa_nonempty := hκMs
      isHall_K := hAHall₀
      A_eq := hKeq.symm
      Z_eq := rfl }
  obtain ⟨-, -, huniqSylow⟩ :=
    FNI_kappa_fixed_prime_centralizer_and_sylow_uniqueness h₂ h₄ h₉ G Mstar A K (A ⊔ K) hsetupMs
  obtain ⟨hQuniq', -⟩ := huniqSylow (Nat.card ↥K) (pCoreOf (Nat.card ↥K) Mstar) hqprime
    dvd_rfl ⟨hQsylow.1, hQsylow.2⟩
  have hQuniq : IsUniqueMaximalOvergroup (Prep08.pCoreOfSubgroup (Nat.card ↥K) Mstar) Mstar :=
    ⟨hs.isCoatom_Mstar, hQsylow.1, fun T hT hQT => hQuniq' T hT hQT⟩
  have hQsyl08 :
      Prep08.IsSylowOf (Nat.card ↥K) (Prep08.pCoreOfSubgroup (Nat.card ↥K) Mstar) Mstar :=
    (Prep08.isSylowOf_iff_natCard hqprime (Prep08.pCoreOfSubgroup_le _ _)).2 hQsylow.2
  have hQnorm : Mstar ≤ normalizer
      ((Prep08.pCoreOfSubgroup (Nat.card ↥K) Mstar : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le (Nat.card ↥K) Mstar)).1 hQnormal
  refine ⟨fun p hp B hBD hBplane => ?_, fun p hp => ?_⟩
  ·
    obtain ⟨hpp, hpσH, hprankH⟩ := mem_tauTwoPrimes_iff.1 hp
    have hBH : B ≤ H := hBD.trans inf_le_left
    have hBMs : B ≤ Mstar := hBD.trans inf_le_right
    have hBplane04 : _root_.CFSG.FeitThompson.IsElementaryAbelianPlane p B :=
      nonempty_mulEquiv_pi_of_isElementaryAbelian hpp hBplane.1 hBplane.2
    obtain ⟨hBnormD, -, -, -, -⟩ := h₅ G hG04 p H B (H ⊓ Mstar)
      ⟨hs.isCoatom_H, hpp, hpσH, hBH, hBplane04⟩ ⟨hs.isCoatom_H, hHsplit⟩ hBD
    have hBab : IsMulCommutative ↥B := hBplane.isMulCommutative
    have hBnil : Group.IsNilpotent ↥B := isNilpotent_of_isMulCommutative ↥B
    have hBF : B ≤ fittingOfNormal (H ⊓ Mstar) := by
      rw [← map_fittingRaw_subtype_eq_fittingOfNormal]
      exact le_map_fittingRaw_of_le_normalizer hBD hBnormD hBnil
    have hBK : ⁅B, K⁆ = ⊥ := commutator_eq_bot_of_le_of_isMulCommutative hFDab hBF hKF
    have hKB : ⁅K, B⁆ = ⊥ := commutator_eq_bot_of_le_of_isMulCommutative hFDab hKF hBF
    have hBcard : Nat.card ↥(B.subgroupOf Mstar) = p ^ 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBMs).toEquiv, hBplane.2]
    have hpσMs : p ∈ sigmaPrimes Mstar := by
      by_contra hpn
      have hsolv : Group.IsSolvable ↥Mstar := hG.isSolvable_of_ne_top Mstar hs.isCoatom_Mstar.1
      have hBπ : IsPiSubgroup ((sigmaPrimes Mstar)ᶜ) (B.subgroupOf Mstar) := by
        refine isPiSubgroup_iff.2 fun t ht => ?_
        have htp : t.Prime := Nat.prime_of_mem_primeFactors ht
        have htd : t ∣ p ^ 2 := hBcard ▸ Nat.dvd_of_mem_primeFactors ht
        rw [(Nat.prime_dvd_prime_iff_eq htp hpp).1 (htp.dvd_of_dvd_pow htd)]
        exact hpn
      obtain ⟨E', hE'hall, hBE'⟩ := exists_isHallSubgroup_ge_of_isPiSubgroup hBπ
      have hEMs : E'.map Mstar.subtype ≤ Mstar := map_subtype_le _
      have hEsub : (E'.map Mstar.subtype).subgroupOf Mstar = E' := by
        rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Mstar.subtype_injective]
      have hE'hall2 : IsHallSubgroup ((sigmaPrimes Mstar)ᶜ)
          ((E'.map Mstar.subtype).subgroupOf Mstar) := by rw [hEsub]; exact hE'hall
      have hBE : B ≤ E'.map Mstar.subtype := by
        have h2 := Subgroup.map_mono (f := Mstar.subtype) hBE'
        rwa [Subgroup.map_subgroupOf_eq_of_le hBMs] at h2
      obtain ⟨hsup, hinf⟩ := sup_eq_and_inf_eq_bot_of_isHallSubgroup_compl
        (sigmaCore_le Mstar) hEMs (isHallSubgroup_iff_isHallPiSubgroup.2 hSMs.2)
        hE'hall2 (hEMs.trans (le_normalizer_sigmaCore Mstar))
      have hcompl : FreeCore.IsInternalSemidirectProduct Mstar (sigmaCore Mstar)
          (E'.map Mstar.subtype) :=
        ⟨hsup, le_normalizer_sigmaCore Mstar, disjoint_iff.2 hinf⟩
      obtain ⟨-, -, hCB, -, -⟩ := h₅ G hG04 p Mstar B (E'.map Mstar.subtype)
        ⟨hs.isCoatom_Mstar, hpp, hpn, hBMs, hBplane04⟩ ⟨hs.isCoatom_Mstar, hcompl⟩ hBE
      have hKE : K ≤ E'.map Mstar.subtype :=
        le_trans (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hKB) hCB
      have hqmem : Nat.card ↥K
          ∈ (Nat.card ↥((E'.map Mstar.subtype).subgroupOf Mstar)).primeFactors := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEMs).toEquiv]
        exact Nat.mem_primeFactors.2 ⟨hqprime, Subgroup.card_dvd_of_le hKE, Nat.card_pos.ne'⟩
      exact isPiNumber_iff.1 hE'hall2.natCard _ hqmem hqσMs
    have hBπMs : IsPiSubgroup (sigmaPrimes Mstar) (B.subgroupOf Mstar) := by
      refine isPiSubgroup_iff.2 fun t ht => ?_
      have htp : t.Prime := Nat.prime_of_mem_primeFactors ht
      have htd : t ∣ p ^ 2 := hBcard ▸ Nat.dvd_of_mem_primeFactors ht
      rw [(Nat.prime_dvd_prime_iff_eq htp hpp).1 (htp.dvd_of_dvd_pow htd)]
      exact hpσMs
    have hBS : B ≤ sigmaCore Mstar := by
      have h1 := hSMs.2.le_of_isPiSubgroup hBπMs
      have h2 := Subgroup.map_mono (f := Mstar.subtype) h1
      rwa [Subgroup.map_subgroupOf_eq_of_le hBMs,
        Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le Mstar)] at h2
    have hBFMs : B ≤ fittingOfNormal Mstar :=
      le_trans (le_inf hBS (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hBK)) hCF
    refine ⟨hqprime, hBK, hpσMs, ?_, hQsyl08, hQnorm, hQuniq⟩
    rw [fittingOf_eq_fittingOfNormal]
    exact hBFMs
  ·
    obtain ⟨hpp, hpσH, hprankH⟩ := mem_tauTwoPrimes_iff.1 hp
    have hfq := Fact.mk hpp
    obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow p ↥(H ⊓ Mstar)))
    have hP'le : (P : Subgroup ↥(H ⊓ Mstar)).map (H ⊓ Mstar).subtype ≤ H ⊓ Mstar :=
      map_subtype_le _
    have hpS : ¬ p ∣ Nat.card ↥(sigmaCore H) :=
      not_dvd_natCard_sigmaCore_of_notMem_sigmaPrimes hpp hpσH
    have hfac : (Nat.card ↥H).factorization p = (Nat.card ↥(H ⊓ Mstar)).factorization p :=
      factorization_eq_of_isInternalSemidirectProduct hHsplit hpS
    have hP'card : Nat.card ↥((P : Subgroup ↥(H ⊓ Mstar)).map (H ⊓ Mstar).subtype)
        = p ^ (Nat.card ↥H).factorization p := by
      rw [Subgroup.card_subtype, P.card_eq_multiplicity, hfac]
    obtain ⟨B, hBP, hBea, hBcard⟩ :=
      exists_isElementaryAbelian_natCard_eq_sq_le_of_isSylow hpp (hP'le.trans inf_le_left) hP'card
        hprankH
    exact ⟨B, hBP.trans hP'le, hBea, hBcard⟩

end

end CFSG.FeitThompson.Proofs
