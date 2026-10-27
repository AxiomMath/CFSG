module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.NoncyclicSigmaNormalizer
import CFSG.FeitThompson.Local.SigmaNormalizerNonconjugateMaximal
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.OddOrder.SigmaPrimesWellDefined
import CFSG.FeitThompson.OddOrder.PGroupNormalizerCondition
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

open Subgroup CFSG.FeitThompson CFSG.FeitThompson

universe u

variable {G : Type u} [Group G] [Finite G] {q : ℕ}

theorem eq_of_isSylowSubgroupOf_of_isPGroup (hq : q.Prime) {S K N : Subgroup G}
    (hS : IsSylowSubgroupOf q S N) (hSK : S ≤ K) (hKN : K ≤ N) (hK : IsPGroup q ↥K) : K = S := by
  have := Fact.mk hq
  obtain ⟨n, hn⟩ := hK.exists_card_eq
  have hle : n ≤ (Nat.card ↥N).factorization q :=
    (hq.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 (hn ▸ Subgroup.card_dvd_of_le hKN)
  have hcard : Nat.card ↥K ≤ Nat.card ↥S := by
    rw [hn, hS.2]; exact Nat.pow_le_pow_right hq.pos hle
  exact (Subgroup.eq_of_le_of_card_ge hSK hcard).symm

theorem eq_of_inf_normalizer_le (hq : q.Prime) {S Q : Subgroup G} (hSQ : S ≤ Q)
    (hQ : IsPGroup q ↥Q) (h : Q ⊓ normalizer (S : Set G) ≤ S) : Q = S := by
  have := Fact.mk hq
  by_contra hne
  have hlt : S.subgroupOf Q < ⊤ :=
    lt_top_iff_ne_top.2 fun htop => hne (le_antisymm (Subgroup.subgroupOf_eq_top.1 htop) hSQ)
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hgrow := lt_normalizer_of_natCard_eq_pow hq hn hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hSQ] at hgrow
  refine absurd hgrow (not_lt_of_ge fun x hx => ?_)
  exact Subgroup.mem_subgroupOf.2 (h ⟨x.2, Subgroup.mem_subgroupOf.1 hx⟩)

theorem exists_isSylowSubgroupOf_ge (hq : q.Prime) {X K : Subgroup G} (hKX : K ≤ X)
    (hK : IsPGroup q ↥K) : ∃ P : Subgroup G, K ≤ P ∧ IsSylowSubgroupOf q P X := by
  have := Fact.mk hq
  obtain ⟨S, hS⟩ := (hK.comap_of_injective X.subtype X.subtype_injective).exists_le_sylow
  refine ⟨(S : Subgroup ↥X).map X.subtype, ?_, Subgroup.map_subtype_le _, ?_⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le hKX]
    exact Subgroup.map_mono hS
  · rw [Subgroup.card_subtype]; exact S.card_eq_multiplicity

theorem dvd_natCard_of_isPGroup_of_ne_bot (hq : q.Prime) {Y K : Subgroup G} (hYq : IsPGroup q ↥Y)
    (hY : Y ≠ ⊥) (hYK : Y ≤ K) : q ∣ Nat.card ↥K := by
  have := Fact.mk hq
  obtain ⟨n, hn⟩ := hYq.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hY (Subgroup.card_eq_one.1 (by simpa using hn))
  exact (dvd_pow_self q hn0).trans (hn ▸ Subgroup.card_dvd_of_le hYK)

theorem normalizer_le_of_isSylowSubgroupOf_inf
    (h₁ : Statements.FTS_plane_maximal_overgroups.{u}) (hG : IsOddOrderMinimalSimple G)
    {M T : Subgroup G} (hM : IsCoatom M) (hq : q.Prime) (hqσ : q ∈ sigmaPrimes M)
    {Y S : Subgroup G} (hYS : Y ≤ S) (hYT : normalizer (Y : Set G) ≤ T)
    (hS : IsSylowSubgroupOf q S (M ⊓ T)) : normalizer (S : Set G) ≤ M := by
  have hSM : S ≤ M := hS.1.trans inf_le_left
  have hSq : IsPGroup q ↥S := IsPGroup.of_card hS.2
  by_cases hcyc : IsCyclic ↥S
  ·
    have hNT : normalizer (S : Set G) ≤ T :=
      (le_normalizer_of_le_of_isCyclic hYS le_rfl).trans hYT
    obtain ⟨Q, hSQ, hQ⟩ := exists_isSylowSubgroupOf_ge hq hSM hSq
    have hQq : IsPGroup q ↥Q := IsPGroup.of_card hQ.2
    have hinf : Q ⊓ normalizer (S : Set G) = S :=
      eq_of_isSylowSubgroupOf_of_isPGroup hq hS (le_inf hSQ Subgroup.le_normalizer)
        (le_inf (inf_le_left.trans hQ.1) (inf_le_right.trans hNT)) (hQq.to_le inf_le_left)
    have hQS : Q = S := eq_of_inf_normalizer_le hq hSQ hQq hinf.le
    obtain ⟨-, P, hPM, hPcard, hPN⟩ := (mem_sigmaPrimes_iff_exists_subgroup hq).1 hqσ
    exact normalizer_le_of_normalizer_le_of_card_eq hq hPM hPcard hSM (hQS ▸ hQ.2) hPN
  ·
    exact FTS_noncyclic_sigma_normalizer h₁ G
      ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
      M S q hM hqσ hSM hSq hcyc

theorem isSylowSubgroupOf_of_normalizer_le (hq : q.Prime) {M T S : Subgroup G}
    (hS : IsSylowSubgroupOf q S (M ⊓ T)) (hNM : normalizer (S : Set G) ≤ M) :
    IsSylowSubgroupOf q S T := by
  have hSq : IsPGroup q ↥S := IsPGroup.of_card hS.2
  obtain ⟨R, hSR, hR⟩ := exists_isSylowSubgroupOf_ge hq (hS.1.trans inf_le_right) hSq
  have hRq : IsPGroup q ↥R := IsPGroup.of_card hR.2
  have hinf : R ⊓ normalizer (S : Set G) = S :=
    eq_of_isSylowSubgroupOf_of_isPGroup hq hS (le_inf hSR Subgroup.le_normalizer)
      (le_inf (inf_le_right.trans hNM) (inf_le_left.trans hR.1)) (hRq.to_le inf_le_left)
  have hRS : R = S := eq_of_inf_normalizer_le hq hSR hRq hinf.le
  exact ⟨hRS ▸ hR.1, hRS ▸ hR.2⟩

theorem FBG_sigma_prime_normalizer_embedding_sylows
    (h₁ : Statements.FTS_plane_maximal_overgroups.{u}) :
    Statements.FBG_sigma_prime_normalizer_embedding_sylows.{u} := by
  intro G _ _ hG M T hM hT hMT q hq hqσ Y hYM hY hYq hYT
  have := hG.isSimpleGroup
  have hqodd : Odd q := by
    refine hq.odd_of_ne_two fun h => ?_
    have h2 : (2 : ℕ) ∣ Nat.card G :=
      h ▸ (dvd_natCard_of_mem_sigmaPrimes hqσ).trans (Subgroup.card_subgroup_dvd_card M)
    exact (Nat.not_even_iff_odd.2 hG.odd_natCard) (even_iff_two_dvd.2 h2)
  have hYTle : Y ≤ T := Subgroup.le_normalizer.trans hYT
  refine ⟨?_, ?_, ?_⟩
  ·
    intro g hg
    refine not_exists_conj_smul_eq_of_normalizer_le hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hM hT hMT hqσ (bot_lt_iff_ne_bot.2 hY) hYM hYq hYT ⟨g⁻¹, ?_⟩
    rw [hg, conj_smul_eq_map_conj]
    rfl
  · intro S hS hYS
    have hNM := normalizer_le_of_isSylowSubgroupOf_inf h₁ hG hM hq hqσ hYS hYT hS
    exact ⟨hNM, isSylowSubgroupOf_of_normalizer_le hq hS hNM⟩
  · by_cases hqT : q ∈ sigmaPrimes T
    · exact Or.inl hqT
    refine Or.inr (mem_tauTwoPrimes_iff.2 ⟨hq, hqT, ?_⟩)
    obtain ⟨S, hYS, hS⟩ := exists_isSylowSubgroupOf_ge hq (le_inf hYM hYTle) hYq
    have hNM := normalizer_le_of_isSylowSubgroupOf_inf h₁ hG hM hq hqσ hYS hYT hS
    have hST := isSylowSubgroupOf_of_normalizer_le hq hS hNM
    have hSq : IsPGroup q ↥S := IsPGroup.of_card hS.2
    have hnc : ¬ IsCyclic ↥S := by
      intro hcyc
      refine hqT ((mem_sigmaPrimes_iff_exists_subgroup hq).2
        ⟨dvd_natCard_of_isPGroup_of_ne_bot hq hYq hY hYTle, S, hST.1, hST.2, ?_⟩)
      exact (le_normalizer_of_le_of_isCyclic hYS le_rfl).trans hYT
    have h2 : 2 ≤ elementaryAbelianPRank q ↥T :=
      le_trans (two_le_elementaryAbelianPRank_of_not_isCyclic hq hqodd hSq hnc)
        (elementaryAbelianPRank_le_of_le hq.one_lt hST.1)
    have hle2 : elementaryAbelianPRank q ↥T ≤ 2 := by
      by_contra hcon
      exact hqT (alphaPrimes_subset_sigmaPrimes hG.not_isMulCommutative hG.odd_natCard
        hG.isSolvable_of_ne_top hT (mem_alphaPrimes.2 ⟨hq, by omega⟩))
    omega

end

end CFSG.FeitThompson.Proofs
