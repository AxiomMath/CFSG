module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerOutsideComplement
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerEmbeddingSylows
import CFSG.FeitThompson.Local.AbelianHallTauTwoControlsCentralizers
import CFSG.FeitThompson.Local.AuxiliaryOppositeTauTwoRankOne
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
import CFSG.FeitThompson.Local.BetaPrimesSigmaCompatibility
import CFSG.FeitThompson.Local.KappaPrimeLineFixedEquivalence
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.OddOrder.ExponentComplementCyclicHallAction
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

variable {G : Type u} [Group G]

theorem not_dvd_natCard_of_mem_sigmaPrimes [Finite G] {M E : Subgroup G}
    (hHall : IsHallPiSubgroupOf (sigmaPrimes M) (sigmaCore M) M)
    (hsd : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E) {p : ℕ}
    (hp : p ∈ sigmaPrimes M) : ¬ p ∣ Nat.card ↥E := by
  intro hdvd
  refine hHall.2.notMem_of_mem_primeFactors_index p ?_ hp
  rw [index_subgroupOf_left_eq hsd]
  exact Nat.mem_primeFactors.2 ⟨prime_of_mem_sigmaPrimes hp, hdvd, Nat.card_pos.ne'⟩

theorem natCard_sigmaCore_mul_index [Finite G] (M : Subgroup G) :
    Nat.card ↥(sigmaCore M) * ((sigmaCore M).subgroupOf M).index = Nat.card ↥M := by
  have hK : Nat.card ↥((sigmaCore M).subgroupOf M) = Nat.card ↥(sigmaCore M) :=
    Nat.card_congr (subgroupOfEquivOfLe (sigmaCore_le M)).toEquiv
  rw [← hK]
  exact Subgroup.card_mul_index _

theorem not_dvd_index_subgroupOf_sigmaCore [Finite G] {M : Subgroup G}
    (hHall : IsHallPiSubgroupOf (sigmaPrimes M) (sigmaCore M) M) {p : ℕ}
    (hp : p ∈ sigmaPrimes M) : ¬ p ∣ ((sigmaCore M).subgroupOf M).index := fun hd =>
  hHall.2.notMem_of_mem_primeFactors_index p
    (Nat.mem_primeFactors.2 ⟨prime_of_mem_sigmaPrimes hp, hd, Subgroup.index_ne_zero_of_finite⟩) hp

theorem dvd_natCard_sigmaCore [Finite G] {M : Subgroup G}
    (hHall : IsHallPiSubgroupOf (sigmaPrimes M) (sigmaCore M) M) {p : ℕ}
    (hp : p ∈ sigmaPrimes M) : p ∣ Nat.card ↥(sigmaCore M) := by
  have hpp : p.Prime := prime_of_mem_sigmaPrimes hp
  have hmul := natCard_sigmaCore_mul_index M
  have hdvd : p ∣ Nat.card ↥(sigmaCore M) * ((sigmaCore M).subgroupOf M).index := by
    rw [hmul]; exact dvd_natCard_of_mem_sigmaPrimes hp
  exact ((Nat.Prime.dvd_mul hpp).1 hdvd).resolve_right (not_dvd_index_subgroupOf_sigmaCore hHall hp)

theorem factorization_natCard_sigmaCore_eq [Finite G] {M : Subgroup G}
    (hHall : IsHallPiSubgroupOf (sigmaPrimes M) (sigmaCore M) M) {p : ℕ}
    (hp : p ∈ sigmaPrimes M) :
    (Nat.card ↥(sigmaCore M)).factorization p = (Nat.card ↥M).factorization p := by
  rw [← natCard_sigmaCore_mul_index M,
    Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite]
  simp [Nat.factorization_eq_zero_of_not_dvd (not_dvd_index_subgroupOf_sigmaCore hHall hp)]

theorem dvd_natCard_of_isSylowIn [Finite G] {p : ℕ} (hp : p.Prime) {P X : Subgroup G}
    (hP : Prep06.IsSylowIn p P X) (hdvd : p ∣ Nat.card ↥X) : p ∣ Nat.card ↥P := by
  rw [hP.2]
  exact dvd_pow_self p (hp.factorization_pos_of_dvd Nat.card_pos.ne' hdvd).ne'

theorem dvd_natCard_centralizer_of_commutator_eq_bot [Finite G] {q p : ℕ} (hq : q.Prime)
    {M A P Q : Subgroup G} (hAM : A ≤ M) (hAq : IsPGroup q ↥A) (hQM : Q ≤ M)
    (hQcard : Nat.card ↥Q = q ^ (Nat.card ↥M).factorization q) (hPQ : ⁅P, Q⁆ = ⊥)
    (hpP : p ∣ Nat.card ↥P) : p ∣ Nat.card ↥(centralizer (A : Set G)) := by
  have := Fact.mk hq
  obtain ⟨S, hS⟩ := (exists_sylow_map_subtype_eq_iff hq (P := Q)).2 ⟨hQM, hQcard⟩
  obtain ⟨m, -, hle⟩ := exists_mem_map_conj_le_sylow hAM
    (hAq.comap_of_injective M.subtype M.subtype_injective) S
  rw [hS] at hle
  have hPC : P ≤ centralizer ((A.map (MulAut.conj m : G →* G) : Subgroup G) : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hPQ).trans (Subgroup.centralizer_le hle)
  have hcard : Nat.card ↥(centralizer ((A.map (MulAut.conj m : G →* G) : Subgroup G) : Set G))
      = Nat.card ↥(centralizer (A : Set G)) := by
    rw [← conj_smul_eq_map_conj, centralizer_conj_smul, conj_smul_eq_map_conj]
    exact Subgroup.card_map_of_injective (MulAut.conj m).injective
  exact hcard ▸ hpP.trans (Subgroup.card_dvd_of_le hPC)

theorem FBG_sigma_prime_normalizer_outside_narrow_prime_factor
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_beta_prime_centralizing_sylow.{u})
    (_h₆ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u}) :
    _root_.CFSG.FeitThompson.Statements.FBG_sigma_prime_normalizer_outside_narrow_prime_factor.{u} := by
  intro G _ _ hG M T hM hT hMT q hq hqσ Y hYM hY hYq hYT E hE p hp hpE hpβ hqT
  have := hG.isSimpleGroup
  have hG04 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG06 : _root_.CFSG.FeitThompson.Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨hqτ, -, hsdT⟩ := FBG_sigma_prime_normalizer_outside_complement h₂ h₃ h₇ G hG M T
    hM hT hMT q hq hqσ Y hYM hY hYq hYT hqT
  obtain ⟨hHallM, -, -⟩ := h₁ G hG M hM
  obtain ⟨hHallT, -, -⟩ := h₁ G hG T hT
  have hpσM : p ∉ sigmaPrimes M := fun hmem =>
    not_dvd_natCard_of_mem_sigmaPrimes hHallM hE hmem hpE
  have hpq : p ≠ q := fun h => hpσM (h ▸ hqσ)
  have hpM : p ∣ Nat.card ↥M := hpE.trans (Subgroup.card_dvd_of_le hE.right_le)
  have hop : Odd p := hG.odd_natCard.of_dvd_nat (hpM.trans (Subgroup.card_subgroup_dvd_card M))
  have hoq : Odd q :=
    hG.odd_natCard.of_dvd_nat ((dvd_natCard_of_mem_sigmaPrimes hqσ).trans
      (Subgroup.card_subgroup_dvd_card M))
  have hqβG : q ∉ betaPrimes G := notMem_betaPrimes_of_mem_tauTwoPrimes h₄ hG04 hT hqτ
  have hqβM : q ∉ betaPrimes ↥M := fun h =>
    hqβG ((mem_betaPrimes_subgroup_iff_of_mem_sigmaPrimes hqσ).1 h)
  have hqβT : q ∉ betaPrimes ↥T := fun h =>
    hqT (betaPrimes_subset_sigmaPrimes hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hT h)
  have hpβM : p ∉ betaPrimes ↥M := fun h =>
    hpσM (betaPrimes_subset_sigmaPrimes hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hM h)
  have hpβT : p ∉ betaPrimes ↥T := by
    rw [betaPrimes_subgroup_eq_sigmaPrimes_inter hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hT]
    exact fun h => hpβ h.2
  have hpσT : p ∉ sigmaPrimes T := by
    intro hpT
    have hpJ : ¬ p ∣ Nat.card ↥(M ⊓ T) := not_dvd_natCard_of_mem_sigmaPrimes hHallT hsdT hpT
    obtain ⟨-, hsyl, -⟩ := FBG_sigma_prime_normalizer_embedding_sylows h₇ G hG M T hM hT hMT q
      hq hqσ Y hYM hY hYq hYT
    have hYTle : Y ≤ T := Subgroup.le_normalizer.trans hYT
    obtain ⟨S, hYS, hS⟩ := exists_isSylowSubgroupOf_ge hq (le_inf hYM hYTle) hYq
    obtain ⟨-, hST⟩ := hsyl S hS hYS
    have hrank : elementaryAbelianPRank q ↥T = 2 := (mem_tauTwoPrimes_iff.1 hqτ).2.2
    obtain ⟨A, hAS, hAelem, hAcard⟩ :=
      exists_isElementaryAbelian_natCard_eq_sq_le_of_isSylow hq hST.1 hST.2 hrank
    have hAJ : A ≤ M ⊓ T := hAS.trans hS.1
    have hAT : A ≤ T := hAJ.trans inf_le_right
    have hAM : A ≤ M := hAJ.trans inf_le_left
    have hplane : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane q T A :=
      ⟨hT, hq, hqT, hAT, nonempty_mulEquiv_pi_of_isElementaryAbelian hq hAelem hAcard⟩
    have hCA : centralizer (A : Set G) ≤ M ⊓ T :=
      (h₂ G hG04 q T A (M ⊓ T) hplane ⟨hT, hsdT⟩ hAJ).2.2.1
    have hkey : p ∣ Nat.card ↥(centralizer (A : Set G)) := by
      rcases lt_or_gt_of_ne hpq with hlt | hlt
      · obtain ⟨P, hP, hcomm⟩ := h₅ G hG06 T hT p q hp hq hop hoq hpq hpβT hqβT A 2 hAT
          hAcard (Or.inr hlt)
        have hpP : p ∣ Nat.card ↥P :=
          dvd_natCard_of_isSylowIn hp hP (dvd_natCard_sigmaCore hHallT hpT)
        have hPC : P ≤ centralizer (A : Set G) :=
          Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm)
        exact hpP.trans (Subgroup.card_dvd_of_le hPC)
      · have := Fact.mk hp
        obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow p ↥M))
        have hPM : (P0 : Subgroup ↥M).map M.subtype ≤ M := Subgroup.map_subtype_le _
        have hPcard : Nat.card ↥((P0 : Subgroup ↥M).map M.subtype)
            = p ^ (Nat.card ↥M).factorization p := by
          rw [Subgroup.card_subtype]; exact P0.card_eq_multiplicity
        obtain ⟨Q, hQ, hcomm⟩ := h₅ G hG06 M hM q p hq hp hoq hop (Ne.symm hpq) hqβM hpβM
          ((P0 : Subgroup ↥M).map M.subtype) ((Nat.card ↥M).factorization p) hPM hPcard
          (Or.inr hlt)
        have hpP : p ∣ Nat.card ↥((P0 : Subgroup ↥M).map M.subtype) := by
          rw [hPcard]
          exact dvd_pow_self p (hp.factorization_pos_of_dvd Nat.card_pos.ne' hpM).ne'
        have hQcard : Nat.card ↥Q = q ^ (Nat.card ↥M).factorization q := by
          rw [hQ.2, factorization_natCard_sigmaCore_eq hHallM hqσ]
        exact dvd_natCard_centralizer_of_commutator_eq_bot hq hAM hAelem.isPGroup
          (hQ.1.trans (sigmaCore_le M)) hQcard hcomm hpP
    exact hpJ (hkey.trans (Subgroup.card_dvd_of_le hCA))
  refine ⟨hpσT, fun hdvd => ?_, hsdT⟩
  exact hpσT (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore T) p
    (Nat.mem_primeFactors.2 ⟨hp, hdvd, Nat.card_pos.ne'⟩))

end

end CFSG.FeitThompson.Proofs
