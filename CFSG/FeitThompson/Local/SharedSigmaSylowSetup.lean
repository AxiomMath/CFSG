module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.SigmaComplementExistsNontrivial
import CFSG.FeitThompson.Local.OvergroupJoinsInvariantPrimeSubgroups
import CFSG.FeitThompson.Local.QuotientFittingInvariantComplement
import CFSG.FeitThompson.OddOrder.SigmaSylowIsAmbientSylow
import CFSG.FeitThompson.OddOrder.SigmaPrimesWellDefined
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson
open CFSG.FeitThompson.Prep08 Subgroup Pointwise

universe u

variable {G : Type*} [Group G] [Finite G]

theorem factorization_natCard_eq_of_isHallPiSubgroupOf {π : Set ℕ} {K M : Subgroup G}
    (hHall : IsHallPiSubgroupOf π K M) {q : ℕ} (hqp : q.Prime) (hq : q ∈ π) :
    (Nat.card ↥K).factorization q = (Nat.card ↥M).factorization q := by
  obtain ⟨hKM, hHallπ⟩ := hHall
  have hidx : ¬ q ∣ (K.subgroupOf M).index := fun h =>
    hHallπ.notMem_of_mem_primeFactors_index q
      (Nat.mem_primeFactors.2 ⟨hqp, h, Subgroup.index_ne_zero_of_finite⟩) hq
  have hcard : Nat.card ↥M = Nat.card ↥K * (K.subgroupOf M).index := by
    rw [← natCard_subgroupOf hKM]; exact (Subgroup.card_mul_index _).symm
  rw [hcard, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite]
  simp [Nat.factorization_eq_zero_of_not_dvd hidx]

theorem normalizer_le_of_isSylowOf_of_mem_sigmaPrimes {q : ℕ} {Q M : Subgroup G}
    (hqM : q ∈ sigmaPrimes M) (hQ : IsSylowOf q Q M) : normalizer (Q : Set G) ≤ M := by
  obtain ⟨S, rfl⟩ := hQ
  exact ((mem_sigmaPrimes_iff_forall (prime_of_mem_sigmaPrimes hqM)).1 hqM).2 S

theorem le_sigmaCore_of_isPGroup {q : ℕ} {Q M : Subgroup G} (hqp : q.Prime)
    (hHall : IsHallPiSubgroupOf (sigmaPrimes M) (sigmaCore M) M)
    (hqM : q ∈ sigmaPrimes M) (hQM : Q ≤ M) (hQ : IsPGroup q ↥Q) : Q ≤ sigmaCore M := by
  have := Fact.mk hqp
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hcard : Nat.card ↥(Q.subgroupOf M) = q ^ n := by rw [natCard_subgroupOf hQM, hn]
  have hπ : IsPiSubgroup (sigmaPrimes M) (Q.subgroupOf M) :=
    ((isPiSubgroup_singleton_iff hqp _).2 (IsPGroup.of_card hcard)).mono
      (Set.singleton_subset_iff.2 hqM)
  have hle := hHall.2.le_of_isPiSubgroup hπ
  have h2 := Subgroup.map_mono (f := M.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hQM,
    Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le M)] at h2

theorem exists_isSylowOf_sigmaCore_le_normalizer {M E : Subgroup G} {q : ℕ} (hqp : q.Prime)
    (hsolv : Group.IsSolvable ↥M)
    (hsd : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E)
    (hcop : (Nat.card ↥(sigmaCore M)).Coprime (Nat.card ↥E)) :
    ∃ Q : Subgroup G, IsSylowOf q Q (sigmaCore M) ∧ E ≤ normalizer (Q : Set G) := by
  have hsup : Group.IsSolvable ↥(sigmaCore M ⊔ E : Subgroup G) := by rw [hsd.sup_eq]; exact hsolv
  obtain ⟨Q, hQle, hQHall, -, hEQ⟩ :=
    exists_isHallSubgroup_subgroupOf_ge_le_normalizer_of_le_normalizer (D := sigmaCore M) (A := E)
      (R := ⊥) hsup hsd.right_le_normalizer hcop ({q} : Set ℕ) bot_le
      (by simp [isPiNumber_iff]) (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  exact ⟨Q, (isSylowOf_iff_natCard hqp hQle).2
    (natCard_eq_pow_factorization_of_isHallSubgroup_singleton hqp hQle hQHall), hEQ⟩

omit [Finite G] in
theorem eq_conjSubgroup_of_conjSubgroup_eq {Y Z : Subgroup G} {g h : G}
    (hYZ : Prep08.conjSubgroup Y g = Prep08.conjSubgroup Z h) :
    Y = Prep08.conjSubgroup Z (h * g⁻¹) := by
  ext a
  have hmem := SetLike.ext_iff.1 hYZ (g⁻¹ * a * g)
  simp only [mem_conjSubgroup_iff] at hmem ⊢
  have e1 : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
  have e2 : h * (g⁻¹ * a * g) * h⁻¹ = (h * g⁻¹) * a * (h * g⁻¹)⁻¹ := by group
  rw [e1, e2] at hmem
  exact hmem

theorem FTS_shared_sigma_sylow_setup
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_shared_sigma_sylow_setup.{u} := by
  intro G _ _ hG M L q hM hL hnc hqM hqL
  have : Fintype G := Fintype.ofFinite G
  have hq : q.Prime := prime_of_mem_sigmaPrimes hqM
  have : Fact q.Prime := ⟨hq⟩
  have hG2 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hHall : ∀ X : Subgroup G, IsCoatom X →
      IsHallPiSubgroupOf (sigmaPrimes X) (sigmaCore X) X := fun X hX => (h₁ G hG2 X hX).1
  obtain ⟨⟨E, hEM, hEbot, hsd⟩, hEprop⟩ :=
    FTS_sigma_complement_exists_nontrivial h₁ G hG M hM
  obtain ⟨-, hcop⟩ := hEprop E hEM hsd
  have hsolvM : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hM.1
  obtain ⟨Q, hQS, hEQ⟩ := exists_isSylowOf_sigmaCore_le_normalizer hq hsolvM hsd hcop
  have hQSle : Q ≤ sigmaCore M := hQS.le
  have hQM : Q ≤ M := hQSle.trans (sigmaCore_le M)
  have hQcardS : Nat.card ↥Q = q ^ (Nat.card ↥(sigmaCore M)).factorization q :=
    (isSylowOf_iff_natCard hq hQSle).1 hQS
  have hQcardM : Nat.card ↥Q = q ^ (Nat.card ↥M).factorization q := by
    rw [hQcardS, factorization_natCard_eq_of_isHallPiSubgroupOf (hHall M hM) hq hqM]
  have hQsylM : IsSylowOf q Q M := (isSylowOf_iff_natCard hq hQM).2 hQcardM
  have hQcardG : Nat.card ↥Q = q ^ (Nat.card G).factorization q :=
    natCard_eq_pow_factorization_of_mem_sigmaPrimes hqM hQM hQcardM
  have hQsylG : IsSylowOf q Q (⊤ : Subgroup G) :=
    (isSylowOf_top_iff hq).2 ⟨Sylow.ofCard Q hQcardG, Sylow.coe_ofCard _ _⟩
  have hQbot : Q ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥Q = 1 := by rw [h]; simp
    rw [hQcardM] at h1
    rcases Nat.pow_eq_one.1 h1 with h2 | h2
    · exact hq.ne_one h2
    · exact (hq.factorization_pos_of_dvd Nat.card_pos.ne'
        (dvd_natCard_of_mem_sigmaPrimes hqM)).ne' h2
  have hTcard : Nat.card ↥((((default : Sylow q ↥L) : Subgroup ↥L).map L.subtype : Subgroup G))
      = q ^ (Nat.card G).factorization q :=
    natCard_map_subtype_eq_pow_factorization hqL default
  obtain ⟨c, hc⟩ := exists_conj_smul_eq hTcard hQcardG
  set N : Subgroup G := Prep08.conjSubgroup L c⁻¹ with hNdef
  have hNeq : N = MulAut.conj c • L := by rw [hNdef, Prep08.conjSubgroup, inv_inv]
  have hNcoatom : IsCoatom N := hNeq ▸ isCoatom_conj_smul hL c
  have hQN : Q ≤ N := by
    rw [hNeq, ← hc]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.2 (Subgroup.map_subtype_le _)
  have hcardN : Nat.card ↥N = Nat.card ↥L := by rw [hNeq]; exact natCard_conj_smul c L
  have hqN : q ∈ sigmaPrimes N := by rw [hNeq, sigmaPrimes_conj_smul]; exact hqL
  have hfNG : (Nat.card ↥N).factorization q = (Nat.card G).factorization q := by
    rw [hcardN]; exact factorization_eq_of_mem_sigmaPrimes hqL
  have hfN : (Nat.card ↥(sigmaCore N)).factorization q = (Nat.card ↥N).factorization q :=
    factorization_natCard_eq_of_isHallPiSubgroupOf (hHall N hNcoatom) hq hqN
  have hQsylN : IsSylowOf q Q N := (isSylowOf_iff_natCard hq hQN).2 (by rw [hQcardG, hfNG])
  have hQSN : Q ≤ sigmaCore N :=
    le_sigmaCore_of_isPGroup hq (hHall N hNcoatom) hqN hQN (IsPGroup.of_card hQcardG)
  have hQsylSN : IsSylowOf q Q (sigmaCore N) :=
    (isSylowOf_iff_natCard hq hQSN).2 (by rw [hQcardG, hfN, hfNG])
  have hnormM : normalizer (Q : Set G) ≤ M :=
    normalizer_le_of_isSylowOf_of_mem_sigmaPrimes hqM hQsylM
  have hnormN : normalizer (Q : Set G) ≤ N :=
    normalizer_le_of_isSylowOf_of_mem_sigmaPrimes hqN hQsylN
  refine ⟨E, Q, c⁻¹, hEM, hEbot, hsd, hQbot, hQS, hQsylM, hQsylG, hQsylN, hQsylSN, hEQ,
    le_inf hnormM hnormN, le_inf hEM (hEQ.trans hnormN), le_inf hQSle hQSN, fun x hx => ?_⟩
  refine hnc (x * c) ?_
  have := eq_conjSubgroup_of_conjSubgroup_eq (Y := L) (Z := M) (g := c⁻¹) (h := x) hx
  rwa [inv_inv] at this

end

end CFSG.FeitThompson.Proofs
