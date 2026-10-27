module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.SigmaComplementThreeHallFactors
import CFSG.FeitThompson.Local.TauTwoFactorContainsPlaneRegularActions
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.SigmaTauThreePrimesDerivedContainment
import CFSG.FeitThompson.Local.PrimeCentralizerMinimalFittingAbelian
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

variable {G : Type*} [Group G]

theorem pow_conj_eq_one_iff {p : ℕ} (g n : G) : (g * n * g⁻¹) ^ p = 1 ↔ n ^ p = 1 := by
  rw [conj_pow]
  refine ⟨fun h => ?_, fun h => by rw [h]; group⟩
  have h2 : n ^ p = g⁻¹ * (g * n ^ p * g⁻¹) * g := by group
  rw [h2, h]; group

theorem normalizer_le_normalizer_of_coe_eq_sep {p : ℕ} {A P : Subgroup G}
    (h : (A : Set G) = {x ∈ (P : Set G) | x ^ p = 1}) :
    normalizer (P : Set G) ≤ normalizer (A : Set G) := by
  intro g hg
  have hgP : ∀ n : G, n ∈ (P : Set G) ↔ g * n * g⁻¹ ∈ (P : Set G) := hg
  change ∀ n : G, n ∈ (A : Set G) ↔ g * n * g⁻¹ ∈ (A : Set G)
  intro n
  rw [h]
  simp only [Set.mem_ofPred_eq]
  rw [← hgP n, pow_conj_eq_one_iff]

theorem exists_isSylowSubgroupOf_ge_of_isPGroup_subgroupOf [Finite G] {p : ℕ} [Fact p.Prime]
    {A T : Subgroup G}
    (hAT : A ≤ T) (hA : IsPGroup p (A.subgroupOf T)) :
    ∃ P : Subgroup G, _root_.CFSG.FeitThompson.IsSylowIn p T P ∧ A ≤ P := by
  obtain ⟨S, hS⟩ := hA.exists_le_sylow
  refine ⟨(S : Subgroup ↥T).map T.subtype, ⟨S, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hAT hx⟩, hS (show (⟨x, hAT hx⟩ : ↥T) ∈ A.subgroupOf T from hx), rfl⟩

theorem isPGroup_subgroupOf_of_plane {p : ℕ} {A T : Subgroup G} (hAT : A ≤ T)
    (hA : _root_.CFSG.FeitThompson.IsElementaryAbelianPlane p A) : IsPGroup p (A.subgroupOf T) := by
  refine IsPGroup.of_card (n := 2) ?_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAT).toEquiv]
  exact hA.natCard'

theorem isPiSubgroup_of_plane {π : Set ℕ} {p : ℕ} (hp : p.Prime) (hpπ : p ∈ π) {A : Subgroup G}
    (hA : _root_.CFSG.FeitThompson.IsElementaryAbelianPlane p A) : IsPiSubgroup π A := by
  refine isPiSubgroup_iff.2 fun r hr => ?_
  rw [hA.natCard', Nat.primeFactors_pow _ two_ne_zero, hp.primeFactors,
    Finset.mem_singleton] at hr
  exact hr ▸ hpπ

theorem exists_isPlaneAt_le_of_elementaryAbelianPRank_eq_two [Finite G] {q : ℕ} (hq : q.Prime)
    {K : Subgroup G} (h : elementaryAbelianPRank q ↥K = 2) :
    ∃ B : Subgroup G, B ≤ K ∧ Prep08.IsPlaneAt q B := by
  have h2 : (2 : ℕ) ∈ elementaryAbelianRanks q ↥K :=
    h ▸ elementaryAbelianPRank_mem_elementaryAbelianRanks hq.one_lt
  obtain ⟨H, hcomm, hexp, hcard⟩ := (mem_elementaryAbelianRanks_iff_exists_subgroup hq).1 h2
  refine ⟨H.map K.subtype, Subgroup.map_subtype_le _,
    IsElementaryAbelian.map_subtype (isElementaryAbelian_iff.2 ⟨hcomm, hexp⟩), ?_⟩
  rw [Subgroup.card_subtype, hcard]

theorem factorization_eq_of_isHallPiSubgroup [Finite G] {q : ℕ} (hq : q.Prime) {π : Set ℕ}
    (hqπ : q ∈ π) {E K : Subgroup G} (hle : K ≤ E)
    (hK : IsHallPiSubgroup π (K.subgroupOf E)) :
    (Nat.card ↥K).factorization q = (Nat.card ↥E).factorization q := by
  have hnd : ¬ q ∣ (K.subgroupOf E).index := fun hdvd =>
    hK.notMem_of_mem_primeFactors_index q
      (Nat.mem_primeFactors.2 ⟨hq, hdvd, Subgroup.index_ne_zero_of_finite⟩) hqπ
  have h1 : Nat.card ↥(K.subgroupOf E) * (K.subgroupOf E).index = Nat.card ↥E :=
    Subgroup.card_mul_index _
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h1
  rw [← h1, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite]
  simp [Nat.factorization_eq_zero_of_not_dvd hnd]

theorem FNI_plane_normalizer_rank_two_primes_in_sigma
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_hall_abelian.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_plane_normalizer_rank_two_primes_in_sigma.{u} := by
  intro G _ _ hG p M A E T hA hE hAE hT hNT
  have hG2 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG8 : Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  let _ : Fintype G := Fintype.ofFinite G
  have hfp := Fact.mk hA.prime
  obtain ⟨hEnormA, -, -, -, hNM⟩ := h₃ G hG p M A E hA hE hAE
  have hTM : T ≠ M := fun h => hNM (h ▸ hNT)
  refine ⟨hTM, ?_⟩
  have hAT : A ≤ T := le_trans le_normalizer hNT
  have hET : E ≤ T := le_trans hEnormA hNT
  have hpT : p ∈ sigmaPrimes T := by
    by_contra hpσT
    obtain ⟨-, -, hsyl, -⟩ := h₅ G hG p T A
      ⟨hT, hA.prime, hpσT, hAT, hA.isElementaryAbelianPlane⟩
    obtain ⟨P, hP, hAP⟩ := exists_isSylowSubgroupOf_ge_of_isPGroup_subgroupOf hAT
      (isPGroup_subgroupOf_of_plane hAT hA.isElementaryAbelianPlane)
    obtain ⟨hAsep, hPnT⟩ := (hsyl P hP).2 hAP
    exact hPnT (le_trans (normalizer_le_normalizer_of_coe_eq_sep hAsep) hNT)
  have hAST : A ≤ sigmaCore T :=
    le_sigmaCore_of_isPiSubgroup (h₁ G hG2 T hT).1 hAT
      (isPiSubgroup_of_plane hA.prime hpT hA.isElementaryAbelianPlane)
  intro q hq
  obtain ⟨E₁, E₂, E₃, hsplit, -⟩ := FNI_sigma_complement_three_factors h₁ G hG M E hE
  obtain ⟨hAE₂, -⟩ := FNI_sigma_complement_regular_factors h₃ h₄ h₅ G hG p M A E E₁ E₂ E₃ hA hE
    hAE hsplit.toIsTauHallSplitting
  have hE₂ab : IsMulCommutative ↥E₂ :=
    h₂ G hG2 M hE.isCoatom E hE.isInternalSemidirectProduct E₂ ⟨hsplit.le_E₂, hsplit.isHall_E₂⟩
  obtain ⟨hqp, hqσ, hqrank⟩ := mem_tauTwoPrimes_iff.1 hq
  have hqdvdM : q ∣ Nat.card ↥M := by
    have h := pow_elementaryAbelianPRank_dvd_card (p := q) (X := ↥M) hqp.one_lt
    rw [hqrank] at h
    exact dvd_trans (dvd_pow_self q two_ne_zero) h
  obtain ⟨hπE, hranks, -⟩ := FNI_sigma_complement_prime_data h₁ G hG M E hE
  have hqE : q ∈ _root_.CFSG.FeitThompson.primeDivisorsOf ↥E := by
    rw [hπE]; exact ⟨⟨hqp, hqdvdM⟩, hqσ⟩
  have hrankE₂ : elementaryAbelianPRank q ↥E₂ = 2 := by
    rw [elementaryAbelianPRank_eq_of_le_of_factorization_eq hqp hsplit.le_E₂
      (factorization_eq_of_isHallPiSubgroup hqp hq hsplit.le_E₂ hsplit.isHall_E₂),
      (hranks q hqE).1, hqrank]
  obtain ⟨B, hBE₂, hBplane⟩ := exists_isPlaneAt_le_of_elementaryAbelianPRank_eq_two hqp hrankE₂
  have hAcB : A ≤ centralizer (B : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun y hy =>
      congrArg Subtype.val (hE₂ab.is_comm.comm (⟨y, hBE₂ hy⟩ : ↥E₂) ⟨x, hAE₂ hx⟩)
  by_contra hqσT
  obtain ⟨-, hcent, -⟩ := h₆ G hG8 T B q hT hqp hqσT
    (le_trans hBE₂ (le_trans hsplit.le_E₂ hET)) hBplane
  have hAbot : A ≤ ⊥ := hcent ▸ le_inf hAST hAcB
  have hcard1 : Nat.card ↥A = 1 := by
    rw [le_bot_iff.1 hAbot]
    simp
  rw [hA.isElementaryAbelianPlane.natCard'] at hcard1
  have h2p := hA.prime.two_le
  have : p ^ 2 ≥ 4 := by nlinarith
  omega

end

end CFSG.FeitThompson.Proofs
