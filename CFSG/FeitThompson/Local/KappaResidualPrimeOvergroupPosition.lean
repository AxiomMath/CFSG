module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.KappaNontrivialComplementStructure
import CFSG.FeitThompson.Local.KappaGlobalPairExhaustion
import CFSG.FeitThompson.Local.KappaFixedCoreMeetsNoConjugateMaximal
import CFSG.FeitThompson.Local.CommonSylowNormalizerBetaFactor
import CFSG.FeitThompson.Local.KappaResidualInPrescribedComplement
import CFSG.FeitThompson.Local.KappaResidualComplementNormalizerEscape
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy
import CFSG.FeitThompson.Foundations.NilpotentSylowNormalCharacteristic
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting
import CFSG.FeitThompson.Local.FittingModuleFaithfulAction
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.OddOrder.SigmaPrimesWellDefined

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep03

universe u

variable {G : Type*} [Group G]

theorem conjBy_eq_prep08_conjSubgroup (Y : Subgroup G) (g : G) :
    conjBy Y g = Prep08.conjSubgroup Y g := (rfl)

theorem conjSub_eq_prep08_conjSubgroup (Y : Subgroup G) (g : G) :
    conjSub Y g = Prep08.conjSubgroup Y g := (conj_smul_eq_map_conj g⁻¹ Y).symm

theorem prep09_conjSub_eq_prep08_conjSubgroup (Y : Subgroup G) (g : G) :
    Prep09.conjSub g Y = Prep08.conjSubgroup Y g := (conj_smul_eq_map_conj g⁻¹ Y).symm

theorem natCard_prep08_conjSubgroup (Y : Subgroup G) (g : G) :
    Nat.card ↥(Prep08.conjSubgroup Y g) = Nat.card ↥Y := natCard_conj_smul g⁻¹ Y

theorem sigmaPrimes_prep08_conjSubgroup [Finite G] (M : Subgroup G) (g : G) :
    sigmaPrimes (Prep08.conjSubgroup M g) = sigmaPrimes M := sigmaPrimes_conj_smul M g⁻¹

theorem prep08_conjSubgroup_eq_self_of_mem {M : Subgroup G} {g : G} (hg : g ∈ M) :
    Prep08.conjSubgroup M g = M := Subgroup.conj_smul_eq_self_of_mem (inv_mem hg)

theorem natCard_eq_mul_of_isDirect [Finite G] {Z K A : Subgroup G} (h : IsDirect Z K A) :
    Nat.card ↥Z = Nat.card ↥K * Nat.card ↥A := by
  have hAK : A ≤ normalizer ((K : Subgroup G) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h.2.2.2.2
  rw [← h.2.2.1]
  exact natCard_sup_eq_mul_of_le_normalizer hAK h.2.2.2.1

theorem FTS_kappa_residual_prime_overgroup_position
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_local_pair.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_pair_hall_intersection.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_sigma_prime_separation.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_prime_overgroup_position.{u} := by
  have hexh := FNI_kappa_global_pair_exhaustion h₁ h₂ h₄ h₉
  have hdisjK := FTS_kappa_fixed_core_outside_conjugate_disjoint h₁ h₄ h₉
  intro G _ _ hG M K U A Mstar R H r hs
  have : Fintype G := Fintype.ofFinite G
  have hFBG : CFSG.FeitThompson.IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hFT : CFSG.FeitThompson.IsFTAmbient G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hamb : Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG09 : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hKM : K ≤ M := hs.isHall_K.1
  have hUM : U ≤ M := hs.isHall_U.1
  have hKhall7 : CFSG.FeitThompson.IsHallPiSubgroupOf (kappaPrimes M) K M :=
    ⟨hs.isHall_K.1, hs.isHall_K.2⟩
  have hKres : CFSG.FeitThompson.IsKappaResidualSetup M K U :=
    { isCoatom := hs.isCoatom_M
      kappaPrimes_nonempty := hs.kappa_nonempty
      le_M_K := hKM
      hall_K := hs.isHall_K.2
      le_M_U := hUM
      ne_bot_U := hs.U_ne_bot
      semidirect_M := hs.semidirect_M
      semidirect_UK := hs.semidirect_UK }
  have hKprime : (Nat.card ↥K).Prime :=
    (FBG_kappa_nontrivial_complement_structure h₁ h₄ h₅ h₆ h₇ G hFBG M K U hKres).1
  have hKbot : K ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hKprime; exact hKprime.one_lt.ne' rfl
  have : Fact r.Prime := ⟨hs.prime_r⟩
  have hUab : IsMulCommutative ↥U := hs.isMulCommutative_U
  have hUnil : Group.IsNilpotent ↥U := @isNilpotent_of_isMulCommutative ↥U _ hUab
  obtain ⟨S, hSR⟩ := hs.isSylow_R
  have hSchar : (S : Subgroup ↥U).Characteristic := sylow_characteristic_of_isNilpotent S
  have hUKR : (U ⊔ K : Subgroup G) ≤ normalizer ((R : Subgroup G) : Set G) := by
    rw [← hSR]
    exact le_normalizer_map_subtype_of_characteristic _ hs.semidirect_UK.le_normalizer
  have hUKH : (U ⊔ K : Subgroup G) ≤ H := hUKR.trans hs.normalizer_R_le
  have hKH : K ≤ H := le_sup_right.trans hUKH
  have hUH : U ≤ H := le_sup_left.trans hUKH
  have hrπ : r ∈ {p : ℕ | p.Prime ∧ p ∉ sigmaPrimes M ∧ p ∉ kappaPrimes M} :=
    isPiSubgroup_iff.1 (CFSG.FeitThompson.IsHallPiSubgroupOf.isPiSubgroup ⟨hs.isHall_U.1, hs.isHall_U.2⟩)
      r (Nat.mem_primeFactors.2 ⟨hs.prime_r, hs.r_dvd, Nat.card_pos.ne'⟩)
  have hRU : R ≤ U := hSR ▸ Subgroup.map_subtype_le _
  have hRcardU : Nat.card ↥R = r ^ (Nat.card ↥U).factorization r := by
    rw [← hSR, Subgroup.card_subtype]; exact S.card_eq_multiplicity
  have hfacUM : (Nat.card ↥M).factorization r = (Nat.card ↥U).factorization r :=
    factorization_natCard_eq_of_isHallPiSubgroup_subgroupOf hs.prime_r hs.isHall_U.1
      hs.isHall_U.2 hrπ
  have hRcardM : Nat.card ↥R = r ^ (Nat.card ↥M).factorization r := by
    rw [hRcardU, hfacUM]
  have hrdvdM : r ∣ Nat.card ↥M := hs.r_dvd.trans (Subgroup.card_dvd_of_le hUM)
  have hHM : ∀ g : G, H ≠ Prep08.conjSubgroup M g := by
    intro g hHeq
    have hcard : Nat.card ↥H = Nat.card ↥M := by
      rw [hHeq, natCard_prep08_conjSubgroup]
    have hrσH : r ∈ sigmaPrimes H := by
      rw [mem_sigmaPrimes_iff_exists_subgroup hs.prime_r]
      exact ⟨hcard ▸ hrdvdM, R, hRU.trans hUH, by rw [hRcardM, hcard], hs.normalizer_R_le⟩
    rw [hHeq, sigmaPrimes_prep08_conjSubgroup] at hrσH
    exact hrπ.2.1 hrσH
  have hKsetup : Prep03.IsKappaSetup G M K A (K ⊔ A) :=
    { ambient := hamb
      isCoatom := hs.isCoatom_M
      kappa_nonempty := hs.kappa_nonempty
      isHall_K := isHallPiOf_of_isHallPiSubgroupOf hKhall7
      A_eq := hs.A_eq
      Z_eq := rfl }
  obtain ⟨Ms, ⟨hMsCo, hMsEx⟩, hMsUniq, -, hAne, hAhall, hcentK, hZdir, -, -, -, -, -, -⟩ :=
    h₂ G M K A (K ⊔ A) hKsetup
  have hMsEqStar : Mstar = Ms := hMsUniq Mstar hs.isCoatom_Mstar hs.exists_prime_order_le_K
  subst hMsEqStar
  have hcentK' : sigmaCore Mstar ⊓ centralizer ((A : Subgroup G) : Set G) = K := hcentK
  have hKSMs : K ≤ sigmaCore Mstar := by rw [← hcentK']; exact inf_le_left
  obtain ⟨a, haA⟩ : ∃ a : ℕ, a ∈ (Nat.card ↥A).primeFactors := by
    obtain ⟨a, ha, had⟩ := Nat.exists_prime_and_dvd
      (n := Nat.card ↥A) (fun h => hAne (Subgroup.card_eq_one.1 h))
    exact ⟨a, Nat.mem_primeFactors.2 ⟨ha, had, Nat.card_pos.ne'⟩⟩
  have hκMs : (kappaPrimes Mstar).Nonempty := ⟨a, hAhall.2.1 a haA⟩
  have hAhall7 : CFSG.FeitThompson.IsHallPiSubgroupOf (kappaPrimes Mstar) A Mstar :=
    isHallPiSubgroupOf_of_isHallPiOf hAhall (fun _ _ => Iff.rfl)
  have hHMs : ∀ g : G, H ≠ Prep08.conjSubgroup Mstar g := by
    intro g hHeq
    have hgMs : g ∈ Mstar := by
      by_contra hg
      have hbot := hdisjK G hFT Mstar hMsCo hκMs A hAhall7 g hg
      rw [hcentK'] at hbot
      have hKle : K ≤ conjBy Mstar g := by
        rw [conjBy_eq_prep08_conjSubgroup, ← hHeq]; exact hKH
      exact hKbot (le_bot_iff.1 ((le_inf le_rfl hKle).trans hbot.le))
    rw [prep08_conjSubgroup_eq_self_of_mem hgMs] at hHeq
    subst hHeq
    obtain ⟨-, -, hMinter, -⟩ := h₃ G M K A (K ⊔ A) H hKsetup hMsCo hMsEx hMsUniq
    have hUZ : U ≤ (K ⊔ A : Subgroup G) := hMinter ▸ le_inf hUM hUH
    have hrZ : r ∣ Nat.card ↥K * Nat.card ↥A := by
      rw [← natCard_eq_mul_of_isDirect hZdir]
      exact hs.r_dvd.trans (Subgroup.card_dvd_of_le hUZ)
    rcases (Nat.Prime.dvd_mul hs.prime_r).1 hrZ with hrK | hrA
    · exact hrπ.2.2 (isPiSubgroup_iff.1 hKhall7.isPiSubgroup r
        (Nat.mem_primeFactors.2 ⟨hs.prime_r, hrK, Nat.card_pos.ne'⟩))
    · refine hrπ.2.1 ?_
      have hAS : A ≤ sigmaCore M := hs.A_eq ▸ inf_le_left
      exact isPiSubgroup_iff.1 ((isPiSubgroup_sigmaCore M).of_le hAS) r
        (Nat.mem_primeFactors.2 ⟨hs.prime_r, hrA, Nat.card_pos.ne'⟩)
  have hκH : kappaPrimes H = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro p hp
    obtain ⟨g, hg⟩ :=
      hexh G M K A (K ⊔ A) Mstar hKsetup hMsCo hMsEx hMsUniq H hs.isCoatom_H ⟨p, hp⟩
    rcases hg with hg | hg
    · refine hHM g⁻¹ ?_
      rw [← conjSub_eq_prep08_conjSubgroup, ← hg, conjSub_conjSub, mul_inv_cancel, conjSub_one]
    · refine hHMs g⁻¹ ?_
      rw [← conjSub_eq_prep08_conjSubgroup, ← hg, conjSub_conjSub, mul_inv_cancel, conjSub_one]
  refine ⟨hKprime, hUKH, hHM, hHMs, hκH, fun p hp hpK => ?_⟩
  have hqσMs : Nat.card ↥K ∈ sigmaPrimes Mstar :=
    isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore Mstar) _ (Nat.mem_primeFactors.2
      ⟨hKprime, Subgroup.card_dvd_of_le hKSMs, Nat.card_pos.ne'⟩)
  have hpq : p = Nat.card ↥K := (Nat.prime_dvd_prime_iff_eq hp hKprime).1 hpK
  have hsep : sigmaPrimes Mstar ∩ sigmaPrimes H = ∅ :=
    h₈ G hG09 Mstar H hMsCo hs.isCoatom_H
      (fun g => by rw [prep09_conjSub_eq_prep08_conjSubgroup]; exact hHMs g)
  intro hpH
  rw [Set.eq_empty_iff_forall_notMem] at hsep
  exact hsep p ⟨hpq ▸ hqσMs, hpH⟩

end

end CFSG.FeitThompson.Proofs
