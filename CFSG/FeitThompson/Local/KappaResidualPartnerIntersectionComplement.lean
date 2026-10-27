module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.KappaResidualContainingComplementFitting
import CFSG.FeitThompson.Local.OppositeSigmaPlaneCoreIntersection
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.PlaneNormalizerRankTwoPrimesInSigma
import CFSG.FeitThompson.Local.KappaHallThirdFactorSupportedComplement
import CFSG.FeitThompson.Local.KappaResidualComplementNormalizerEscape
import CFSG.FeitThompson.Local.KappaPrimeLineFixedEquivalence
import CFSG.FeitThompson.Local.CompetingMaximalFittingPrimeSupport
import CFSG.FeitThompson.OddOrder.ConjugateAffineIntersection
import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G]

theorem sigmaCore_inf_sigmaCore_eq_bot_of_sigmaPrimes_disjoint [Finite G] {N T : Subgroup G}
    (h : sigmaPrimes N ∩ sigmaPrimes T = ∅) : sigmaCore N ⊓ sigmaCore T = ⊥ := by
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
    (show Nat.card ↥(sigmaCore N ⊓ sigmaCore T) ≠ 1 from fun h' =>
      hne (Subgroup.card_eq_one.1 h'))
  refine Set.eq_empty_iff_forall_notMem.1 h p ⟨?_, ?_⟩
  · exact isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore N) p (Nat.mem_primeFactors.2
      ⟨hp, hpd.trans (Subgroup.card_dvd_of_le inf_le_left), Nat.card_pos.ne'⟩)
  · exact isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore T) p (Nat.mem_primeFactors.2
      ⟨hp, hpd.trans (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩)

theorem kappa_residual_partner_intersection_complement [Finite G]
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_local_pair.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_free_nonfitting_prime_alternative.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_prime_overgroup_position.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_sigma_prime_separation.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_fixed_line_centralizer_unique.{u})
    (hG : IsFTAmbient G) {r : ℕ} {M K U A Mstar R H : Subgroup G}
    (hP : IsKappaResidualPartner r M K U A Mstar R H) :
    FreeCore.IsInternalSemidirectProduct H (sigmaCore H) (H ⊓ Mstar) ∧
      K ≤ fittingOfNormal (H ⊓ Mstar) := by
  have hfit := FTS_kappa_residual_containing_complement_fitting h₁ h₂ h₃ h₄ h₅ h₈
  have hopp := FTS_opposite_sigma_plane_core_intersection h₆
  have hpd := FNI_sigma_complement_prime_data h₁
  have : Fintype G := Fintype.ofFinite G
  have hamb : Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hG04 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hG08 : Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable⟩
  have hG09 : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
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
  obtain ⟨hKprime, hUKH, -, hncMs, hkappaH, hKsigmaH⟩ :=
    h₅ G hG08 M K U A Mstar R H r hsetup08
  set q : ℕ := Nat.card ↥K with hq
  have hKH : K ≤ H := le_sup_right.trans hUKH
  have hKsetup : Prep03.IsKappaSetup G M K A (K ⊔ A) :=
    { ambient := hamb
      isCoatom := hP.config.isCoatom
      kappa_nonempty := hP.config.kappaPrimes_nonempty
      isHall_K := isHallPiOf_of_isHallPiSubgroupOf hP.config.isHallKappa
      A_eq := hP.A_eq
      Z_eq := rfl }
  obtain ⟨Ms, -, hMsUniq, -, -, -, hcentK, -, -, -, -, -, -, -, -⟩ :=
    h₂ G M K A (K ⊔ A) hKsetup
  have hMsEqStar : Mstar = Ms :=
    hMsUniq Mstar hP.isCoatom_Mstar hP.exists_prime_order_normalizer_le
  subst hMsEqStar
  have hcentK' : sigmaCore Mstar ⊓ centralizer (A : Set G) = K := hcentK
  have hKSMs : K ≤ sigmaCore Mstar := by rw [← hcentK']; exact inf_le_left
  have hqσMs : q ∈ sigmaPrimes Mstar :=
    isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore Mstar) q (Nat.mem_primeFactors.2
      ⟨hKprime, Subgroup.card_dvd_of_le hKSMs, Nat.card_pos.ne'⟩)
  have hqσH : q ∉ sigmaPrimes H := hKsigmaH q hKprime dvd_rfl
  obtain ⟨⟨D, hDH, hsemi, hKD⟩, hall⟩ := hfit G hG r M K U A Mstar R H hP
  obtain ⟨hKF, hDMs⟩ := hall D hDH hsemi hKD
  have hsep : sigmaPrimes Mstar ∩ sigmaPrimes H = ∅ :=
    h₇ G hG09 Mstar H hP.isCoatom_Mstar hP.isCoatom_H fun g h => hncMs g h
  have hcores : sigmaCore H ⊓ sigmaCore Mstar = ⊥ :=
    sigmaCore_inf_sigmaCore_eq_bot_of_sigmaPrimes_disjoint
      (by rw [Set.inter_comm]; exact hsep)
  have hVbot : sigmaCore H ⊓ Mstar = ⊥ := by
    by_contra hV
    set V : Subgroup G := sigmaCore H ⊓ Mstar with hVdef
    set B : Subgroup G := sigmaCore Mstar ⊓ H with hBdef
    have hVL : V ≤ H ⊓ Mstar := le_inf (inf_le_left.trans (sigmaCore_le H)) inf_le_right
    have hBL : B ≤ H ⊓ Mstar := le_inf inf_le_right (inf_le_left.trans (sigmaCore_le Mstar))
    have hVn : H ⊓ Mstar ≤ normalizer (V : Set G) := fun x hx =>
      mem_normalizer_inf (le_normalizer_sigmaCore H (Subgroup.mem_inf.1 hx).1)
        (Subgroup.le_normalizer (Subgroup.mem_inf.1 hx).2)
    have hBn : H ⊓ Mstar ≤ normalizer (B : Set G) := fun x hx =>
      mem_normalizer_inf (le_normalizer_sigmaCore Mstar (Subgroup.mem_inf.1 hx).2)
        (Subgroup.le_normalizer (Subgroup.mem_inf.1 hx).1)
    have hVB : V ⊓ B = ⊥ := le_bot_iff.1 (le_trans
      (inf_le_inf inf_le_left inf_le_left) (le_of_eq hcores))
    have hVC : V ≤ centralizer (B : Set G) :=
      le_centralizer_of_le_normalizer_of_inf_eq_bot hVL hBL hVn hBn hVB
    have hKB : K ≤ B := le_inf hKSMs hKH
    have hcH : sigmaCore H ⊓ centralizer (K : Set G) ≠ ⊥ := by
      refine fun hc => hV ?_
      refine le_bot_iff.1 (le_trans (le_inf inf_le_left ?_) (le_of_eq hc))
      exact hVC.trans (Subgroup.centralizer_le hKB)
    have hqodd : Odd q := hG.odd_natCard.of_dvd_nat
      (hq ▸ (Subgroup.card_dvd_of_le (le_top : K ≤ ⊤)).trans (by simp))
    have hqD : q ∣ Nat.card ↥D := hq ▸ Subgroup.card_dvd_of_le hKD
    have hsc : _root_.CFSG.FeitThompson.IsSigmaComplement H D := ⟨hP.isCoatom_H, hsemi⟩
    obtain ⟨-, hranks, -⟩ := hpd G hG04 H D hsc
    obtain ⟨hrankeq, hrankle⟩ := hranks q ⟨hKprime, hqD⟩
    have hrank1 : ¬ elementaryAbelianPRank q ↥H ≤ 1 := by
      intro hle
      obtain ⟨S, hS⟩ :=
        exists_isCyclic_sylow_of_elementaryAbelianPRank_le_one H hKprime hqodd hle
      refine Set.eq_empty_iff_forall_notMem.1 hkappaH q ?_
      exact (mem_kappaPrimes_iff_inf_centralizer_ne_bot hKprime hqσH ⟨S, hS⟩ hKH hq.symm).2 hcH
    have hrank2 : elementaryAbelianPRank q ↥H = 2 := by omega
    obtain ⟨B₀, hB₀D, hB₀plane⟩ :=
      exists_isPlaneAt_le_of_elementaryAbelianPRank_eq_two hKprime (hrankeq.trans hrank2)
    exact hV (hopp G hG08 Mstar H B₀ q hP.isCoatom_Mstar hP.isCoatom_H hqσMs hqσH
      (le_inf (hB₀D.trans hDMs) (hB₀D.trans hDH)) hB₀plane)
  have hHMs : H ⊓ Mstar = D := by
    refine le_antisymm (fun x hx => ?_) (le_inf hDH hDMs)
    obtain ⟨hxH, hxMs⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨s, hs, d, hd, hxsd⟩ := hsemi.exists_mul hxH
    have hsMs : s ∈ Mstar := by
      have hsx : s = x * d⁻¹ := by rw [hxsd]; group
      rw [hsx]
      exact mul_mem hxMs (inv_mem (hDMs hd))
    have hs1 : s = 1 := by
      have hmem := hVbot ▸ Subgroup.mem_inf.2 (⟨hs, hsMs⟩ : s ∈ sigmaCore H ∧ s ∈ Mstar)
      simpa using hmem
    rw [hxsd, hs1, one_mul]
    exact hd
  rw [hHMs]
  exact ⟨hsemi, hKF⟩

theorem FTS_kappa_residual_partner_intersection_complement
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_local_pair.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_free_nonfitting_prime_alternative.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_prime_overgroup_position.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_sigma_prime_separation.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_partner_intersection_complement.{u} := by
  intro G _ _ hG r M K U A Mstar R H hP
  exact kappa_residual_partner_intersection_complement h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ hG hP

end

end CFSG.FeitThompson.Proofs
