module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.NonconjugateIntersectionExcludesTauTwo
import CFSG.FeitThompson.Local.NonconjugateIntersectionPrimeCentralization
import CFSG.FeitThompson.Local.NonconjugateIntersectionTauOneBeta
import CFSG.FeitThompson.Local.TauOneHallFixedCentralizer
import CFSG.FeitThompson.Local.OutsideSigmaNormalizerRankTwoPlane
import CFSG.FeitThompson.Local.NonuniqueScnAuxiliaryPrime
import CFSG.FeitThompson.OddOrder.SigmaPrimesWellDefined
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep09 (conjSub)

universe u

variable {G : Type u} [Group G]

theorem forall_ne_conjSub_of_normalizer_le [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) {M L P : Subgroup G} {p : ℕ}
    (hL : IsCoatom L) (hp : p.Prime) (hpM : p ∉ sigmaPrimes M)
    (hrankM : elementaryAbelianPRank p ↥M = 1) (hPcard : Nat.card ↥P = p)
    (hNPL : normalizer (P : Set G) ≤ L) : ∀ g : G, L ≠ conjSub g M := by
  intro g hg
  have hσ : sigmaPrimes L = sigmaPrimes M := by
    rw [hg]; exact sigmaPrimes_conj_smul M g⁻¹
  have hpL : p ∉ sigmaPrimes L := by rw [hσ]; exact hpM
  have hrk : elementaryAbelianPRank p ↥L = elementaryAbelianPRank p ↥M := by
    rw [hg]; exact elementaryAbelianPRank_conj_smul hp.one_lt g⁻¹ M
  have h2 := elementaryAbelianPRank_eq_two_of_notMem_sigmaPrimes hna hodd hsolv hL hp hpL hPcard
    hNPL
  rw [hrk, hrankM] at h2
  omega

theorem le_centralizer_inf_of_forall_notMem_tau1Primes [Finite G]
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_prime_normalizer_narrow_rank_bound.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (hG : IsFBGAmbient G) {M E L X : Subgroup G} (hM : IsCoatom M) (hEM : E ≤ M)
    (hsd : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E) (hL : IsCoatom L)
    (hnc : ∀ g : G, L ≠ conjSub g M) (hXEL : X ≤ E ⊓ L)
    (hπ : ∀ s ∈ (Nat.card ↥X).primeFactors, s ∉ tau1Primes L) :
    X ≤ centralizer ((sigmaCore M ⊓ L : Subgroup G) : Set G) := by
  have hXML : X ≤ M ⊓ L := hXEL.trans (inf_le_inf_right L hEM)
  by_cases hC : ⁅sigmaCore M ⊓ L, M ⊓ L⁆ = ⊥
  · rw [Subgroup.commutator_comm] at hC
    exact hXML.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hC)
  · refine le_centralizer_of_forall_sylow_map_le_centralizer fun r hr Q => ?_
    set R : Subgroup G := (Q : Subgroup ↥X).map X.subtype with hRdef
    have hRX : R ≤ X := Subgroup.map_subtype_le _
    have hRp : IsPGroup r ↥R := Q.isPGroup'.map _
    have := Fact.mk hr
    rcases hRp.card_eq_or_dvd with h1 | hdvd
    ·
      rw [Subgroup.card_eq_one.1 h1]; exact bot_le
    · have hrX : r ∣ Nat.card ↥X := hdvd.trans (Subgroup.card_dvd_of_le hRX)
      have hrmem : r ∈ (Nat.card ↥X).primeFactors :=
        Nat.mem_primeFactors.2 ⟨hr, hrX, Nat.card_pos.ne'⟩
      have hrE : r ∣ Nat.card ↥E :=
        hrX.trans (Subgroup.card_dvd_of_le (hXEL.trans inf_le_left))
      have hrL : r ∣ Nat.card ↥L :=
        hrX.trans (Subgroup.card_dvd_of_le (hXEL.trans inf_le_right))
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
        (FBG_nonconjugate_intersection_prime_centralization h₁ h₂ h₅ G hG M L E r
          ⟨hM, hL, hnc, hEM, hsd, hr, hrE, hrL⟩ (hπ r hrmem) hC R (hRX.trans hXML) hRp)

theorem mem_sigmaPrimes_of_commutator_ne_bot [Finite G] [IsSimpleGroup G]
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_prime_normalizer_narrow_rank_bound.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (hG : IsFBGAmbient G) {M E L P : Subgroup G} {p : ℕ}
    (hsetup : IsNonconjugateSetup M L E p) (hPcard : Nat.card ↥P = p)
    (hNPL : normalizer (P : Set G) ≤ L) (hC : ⁅sigmaCore M ⊓ L, M ⊓ L⁆ ≠ ⊥) :
    p ∈ sigmaPrimes L := by
  by_contra hpσ
  have h2 := elementaryAbelianPRank_eq_two_of_notMem_sigmaPrimes hG.not_isMulCommutative
    hG.odd_natCard hG.isSolvable hsetup.isCoatom_L hsetup.prime hpσ hPcard hNPL
  exact FBG_nonconjugate_intersection_excludes_tau_two h₁ h₂ h₅ G hG M L E p hsetup hC
    (mem_tauTwoPrimes_iff.2 ⟨hsetup.prime, hpσ, h2⟩)

theorem FTS_tau_one_three_prime_normalizer_transfer
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_prime_normalizer_narrow_rank_bound.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_beta_prime_centralizing_sylow.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_tau_one_three_prime_normalizer_transfer.{u} := by
  intro G _ _ hG M hM E hEM hsd p hp P hPM hPcard L hL hNPL
  have : Fintype G := Fintype.ofFinite G
  have : IsSimpleGroup G := hG.isSimpleGroup
  have hG01 : IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG04 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG08 : Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hpprime : p.Prime := by
    rcases hp with h | h
    · exact prime_of_mem_tau1Primes h
    · exact prime_of_mem_tau3Primes h
  have hpM : p ∉ sigmaPrimes M := by
    rcases hp with h | h
    · exact notMem_sigmaPrimes_of_mem_tau1Primes h
    · exact notMem_sigmaPrimes_of_mem_tau3Primes h
  have hrankM : elementaryAbelianPRank p ↥M = 1 := by
    rcases hp with h | h
    · exact elementaryAbelianPRank_eq_one_of_mem_tau1Primes h
    · exact elementaryAbelianPRank_eq_one_of_mem_tau3Primes h
  have hpdvdM : p ∣ Nat.card ↥M := by
    rcases hp with h | h
    · exact dvd_natCard_of_mem_tau1Primes h
    · exact dvd_natCard_of_mem_tau3Primes h
  obtain ⟨hπE, -, -⟩ := FNI_sigma_complement_prime_data h₁ G hG04 M E ⟨hM, hsd⟩
  have hpE : p ∣ Nat.card ↥E :=
    (show p ∈ _root_.CFSG.FeitThompson.primeDivisorsOf ↥E by
      rw [hπE]; exact ⟨⟨hpprime, hpdvdM⟩, hpM⟩).2
  have hPL : P ≤ L := Subgroup.le_normalizer.trans hNPL
  have hpL : p ∣ Nat.card ↥L := hPcard ▸ Subgroup.card_dvd_of_le hPL
  have hnc : ∀ g : G, L ≠ conjSub g M :=
    forall_ne_conjSub_of_normalizer_le hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hL hpprime hpM hrankM hPcard hNPL
  have hsetup : IsNonconjugateSetup M L E p := ⟨hM, hL, hnc, hEM, hsd, hpprime, hpE, hpL⟩
  refine ⟨hnc, fun X hXEL hπ =>
    le_centralizer_inf_of_forall_notMem_tau1Primes h₁ h₂ h₅ hG01 hM hEM hsd hL hnc hXEL hπ,
    fun hC => ?_⟩
  have hpσL : p ∈ sigmaPrimes L :=
    mem_sigmaPrimes_of_commutator_ne_bot h₁ h₂ h₅ hG01 hsetup hPcard hNPL hC
  exact ⟨hpσL, fun hpτ1 =>
    (FTS_nonconjugate_intersection_tau_one_beta h₁ h₃ h₄ h₅ h₆ h₇ h₈ h₉ G hG08 M E L p hM hEM hsd
      hL hnc hpτ1 hpσL hC).2⟩

end

end CFSG.FeitThompson.Proofs
