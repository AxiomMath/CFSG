module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.RegularTauAlphaFixedPoints
import CFSG.FeitThompson.Local.CommonSylowNormalizerBetaFactor
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived
import CFSG.FeitThompson.Local.AlphaCoreNormalHall
import CFSG.FeitThompson.Local.BetaPrimesSigmaCompatibility
import CFSG.FeitThompson.Local.AlphaPrimesInSigmaPrimes
import CFSG.FeitThompson.Local.LowRankFittingDerivedNilpotent
import CFSG.FeitThompson.Local.MixedFittingCentralizerConstrained
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.PComplementQuotientSylowRank
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting
import CFSG.FeitThompson.Local.NormalComplementDerivedIntersection
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.RankThreeUniquenessMaximalOvergroup
import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
import CFSG.FeitThompson.Foundations.NormalNilpotentInFitting
import CFSG.FeitThompson.Foundations.NilpotentSylowNormalCharacteristic
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
import CFSG.FeitThompson.Foundations.NilpotentSubgroupNilpotent

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup
  Pointwise

universe u

variable {G : Type u} [Group G]

theorem centralizer_coe_mul_coe (P Q : Subgroup G) :
    centralizer ((P : Set G) * (Q : Set G))
      = centralizer (P : Set G) ⊓ centralizer (Q : Set G) := by
  refine le_antisymm (le_inf ?_ ?_) ?_
  · exact fun x hx => mem_centralizer_iff.2 fun y hy =>
      (mem_centralizer_iff.1 hx) y ⟨y, hy, 1, Q.one_mem, by simp⟩
  · exact fun x hx => mem_centralizer_iff.2 fun y hy =>
      (mem_centralizer_iff.1 hx) y ⟨1, P.one_mem, y, hy, by simp⟩
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    refine mem_centralizer_iff.2 ?_
    rintro y ⟨a, ha, b, hb, rfl⟩
    have h1 := (mem_centralizer_iff.1 hx.1) a ha
    have h2 := (mem_centralizer_iff.1 hx.2) b hb
    rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]

theorem centralizer_coe_sup (P Q : Subgroup G) :
    centralizer ((P ⊔ Q : Subgroup G) : Set G)
      = centralizer (P : Set G) ⊓ centralizer (Q : Set G) := by
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
  refine le_antisymm (le_inf (Subgroup.centralizer_le Set.subset_union_left)
    (Subgroup.centralizer_le Set.subset_union_right)) ?_
  intro x hx
  rw [Subgroup.mem_inf] at hx
  refine mem_centralizer_iff.2 ?_
  rintro y (hy | hy)
  · exact (mem_centralizer_iff.1 hx.1) y hy
  · exact (mem_centralizer_iff.1 hx.2) y hy

theorem prime_dvd_natCard_of_natCard_eq_pow {Q : Subgroup G} {q e : ℕ}
    (hQcard : Nat.card ↥Q = q ^ e) (hQbot : Q ≠ ⊥) : q ∣ Nat.card ↥Q := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exact absurd (Subgroup.card_eq_one.1 (by simpa using hQcard)) hQbot
  · rw [hQcard]; exact dvd_pow_self q he.ne'

theorem natCard_eq_pow_factorization_commutator [Finite G] {M Q : Subgroup G} {q : ℕ}
    (hq : q.Prime) (hQcard : Nat.card ↥Q = q ^ (Nat.card ↥M).factorization q) (hQC : Q ≤ ⁅M, M⁆) :
    Nat.card ↥Q = q ^ (Nat.card ↥(⁅M, M⁆ : Subgroup G)).factorization q := by
  have h1 : q ^ (Nat.card ↥M).factorization q ∣ Nat.card ↥(⁅M, M⁆ : Subgroup G) := by
    rw [← hQcard]; exact Subgroup.card_dvd_of_le hQC
  have h2 : (Nat.card ↥M).factorization q ≤ (Nat.card ↥(⁅M, M⁆ : Subgroup G)).factorization q :=
    (Nat.Prime.pow_dvd_iff_le_factorization hq Nat.card_pos.ne').1 h1
  have h3 : (Nat.card ↥(⁅M, M⁆ : Subgroup G)).factorization q ≤ (Nat.card ↥M).factorization q :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
      (Subgroup.card_dvd_of_le (Subgroup.commutator_le_self M)) q
  rw [hQcard]; congr 1; omega

theorem elementaryAbelianPRank_eq_of_le_of_natCard_eq_pow_factorization [Finite G] {r : ℕ}
    (hr : r.Prime) {R M : Subgroup G} (hRM : R ≤ M)
    (hcard : Nat.card ↥R = r ^ (Nat.card ↥M).factorization r) :
    elementaryAbelianPRank r ↥R = elementaryAbelianPRank r ↥M := by
  have h1 : Nat.card ↥(R.subgroupOf M) = r ^ (Nat.card ↥M).factorization r := by
    rw [natCard_subgroupOf_of_le' hRM, hcard]
  have h2 := elementaryAbelianPRank_eq_of_natCard_eq_pow_factorization hr h1
  rwa [elementaryAbelianPRank_subgroupOf hr.one_lt hRM] at h2

theorem isSylowSubgroupOf_of_isSylowIn_sigmaCore [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) {M : Subgroup G} (hM : IsCoatom M)
    {r : ℕ} (hr : r.Prime) (hrα : r ∈ alphaPrimes ↥M) {R : Subgroup G}
    (hR : Prep06.IsSylowIn r R (sigmaCore M)) : IsSylowSubgroupOf r R M := by
  have hrσ : r ∈ sigmaPrimes M := alphaPrimes_subset_sigmaPrimes hna hodd hsolv hM hrα
  have hfac := factorization_natCard_eq_of_isHallSubgroup
    (isHallSubgroup_subgroupOf_sigmaCore hna hodd hsolv hM) hr hrσ
  rw [natCard_subgroupOf_of_le' (sigmaCore_le M)] at hfac
  exact ⟨hR.1.trans (sigmaCore_le M), by rw [hR.2, ← hfac]⟩

theorem isCoatom_ge_eq_singleton_of_three_le_rank [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) {X M Y : Subgroup G}
    (hM : IsCoatom M) (hXM : X ≤ M) (hrank : 3 ≤ maxElementaryAbelianPRank ↥X)
    (hXY : X ≤ Y) (hY : Y ≠ ⊤) : {T : Subgroup G | IsCoatom T ∧ Y ≤ T} = {M} := by
  obtain ⟨N, hN⟩ := exists_isUniqueMaximalOvergroup_of_three_le_maxElementaryAbelianPRank hna hodd
    hsolv (ne_top_of_le_ne_top hM.1 hXM) hrank
  have hNM : N = M := by
    have h := (isUniqueMaximalOvergroup_iff X N).1 hN
    have hmem : M ∈ {T : Subgroup G | IsCoatom T ∧ X ≤ T} := ⟨hM, hXM⟩
    rw [h] at hmem
    exact hmem.symm
  subst hNM
  exact (isUniqueMaximalOvergroup_iff Y N).1 (hN.mono hXY hY)

theorem isCoatom_ge_eq_singleton_of_normalizer_eq {M Q : Subgroup G} (hM : IsCoatom M)
    (hN : normalizer (Q : Set G) = M) :
    {T : Subgroup G | IsCoatom T ∧ normalizer (Q : Set G) ≤ T} = {M} := by
  ext T
  simp only [Set.mem_singleton_iff, hN]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases eq_or_lt_of_le h.2 with h' | h'
    · exact h'.symm
    · exact absurd (hM.2 T h') h.1.1
  · subst h; exact ⟨hM, le_rfl⟩

theorem alphaPrimes_eq_empty_of_alphaCore_eq_bot [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) {M : Subgroup G} (hM : IsCoatom M)
    (h : alphaCore ↥M = ⊥) : alphaPrimes ↥M = ∅ := by
  have hHall := isHallSubgroup_alphaCore hna hodd hsolv hM
  rw [Set.eq_empty_iff_forall_notMem]
  intro r hr
  have hrp := prime_of_mem_alphaPrimes hr
  have hdvd : r ∣ Nat.card ↥M := Nat.dvd_of_mem_primeFactors (alphaPrimes_subset_primeFactors hr)
  have hidx : (alphaCore ↥M).index = Nat.card ↥M := by rw [h, Subgroup.index_bot]
  have h2 := isPiNumber_compl_iff.1 hHall.index
  rw [hidx] at h2
  exact h2 r (Nat.mem_primeFactors.2 ⟨hrp, hdvd, Nat.card_pos.ne'⟩) hr

theorem isNilpotent_commutator_of_alphaPrimes_eq_empty [Finite G] {M : Subgroup G}
    (hodd : Odd (Nat.card ↥M)) [Group.IsSolvable ↥M] (h : alphaPrimes ↥M = ∅) :
    Group.IsNilpotent ↥(⁅M, M⁆ : Subgroup G) := by
  have hrank : ∀ r : ℕ, r.Prime → elementaryAbelianPRank r ↥(fittingRaw ↥M) ≤ 2 := by
    intro r hr
    have hnot : r ∉ alphaPrimes ↥M := by rw [h]; exact Set.notMem_empty r
    have h3 : ¬ (3 ≤ elementaryAbelianPRank r ↥M) := fun hh => hnot (mem_alphaPrimes.2 ⟨hr, hh⟩)
    exact le_trans (elementaryAbelianPRank_subgroup_le hr.one_lt _) (by omega)
  have hcomm : _root_.commutator ↥M ≤ fittingRaw ↥M := commutator_le_fittingRaw hodd hrank
  rw [commutator_eq_subgroupOf_commutator] at hcomm
  exact (Group.isNilpotent_congr
    (subgroupOfEquivOfLe (Subgroup.commutator_le_self M))).1 (isNilpotent_of_le_fittingRaw hcomm)

theorem le_normalizer_of_isNilpotent_commutator [Finite G] {M Q : Subgroup G} {q : ℕ}
    (hq : q.Prime) (hnil : Group.IsNilpotent ↥(⁅M, M⁆ : Subgroup G)) (hQC : Q ≤ ⁅M, M⁆)
    (hQcard : Nat.card ↥Q = q ^ (Nat.card ↥(⁅M, M⁆ : Subgroup G)).factorization q) :
    M ≤ normalizer (Q : Set G) := by
  have : Fact q.Prime := ⟨hq⟩
  have hc : Nat.card ↥(Q.subgroupOf ⁅M, M⁆)
      = q ^ (Nat.card ↥(⁅M, M⁆ : Subgroup G)).factorization q := by
    rw [natCard_subgroupOf_of_le' hQC, hQcard]
  have hchar : (Q.subgroupOf ⁅M, M⁆).Characteristic := by
    have h := sylow_characteristic_of_isNilpotent (Sylow.ofCard (Q.subgroupOf ⁅M, M⁆) hc)
    rwa [Sylow.coe_ofCard] at h
  have h := le_normalizer_map_subtype_of_characteristic (M := (⁅M, M⁆ : Subgroup G))
    (Q.subgroupOf ⁅M, M⁆) (L := M) (normalizer_commutator_ge_right M M)
  rwa [Subgroup.map_subgroupOf_eq_of_le hQC] at h

theorem FBG_regular_tau_one_sylow_beta_fixed_points
    (h₁ : Statements.FTS_beta_prime_centralizing_sylow.{u}) :
    Statements.FBG_regular_tau_one_sylow_beta_fixed_points.{u} := by
  intro G _ _ hG M hM p q hpq hp hq hptau P hPM hPcard Q hQ hQbot hPnorm hfix hnotuniq
  have hsimple := hG.isSimpleGroup
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hM.1
  have hQM : Q ≤ M := hQ.1
  have hQpg : IsPGroup q ↥Q := IsPGroup.of_card hQ.2
  have hoddM : Odd (Nat.card ↥M) := hG.odd_natCard.of_dvd_nat M.card_subgroup_dvd_card
  have hQnorm : normalizer (Q : Set G) ≠ ⊤ :=
    (normalizer_lt_top_of_isPGroup hG.not_isMulCommutative hq hQbot hQpg).ne
  have hGMOS : Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hQC : Q ≤ ⁅M, M⁆ := by
    have hPs : Group.IsSolvable ↥P := isSolvable_of_le_of_isSolvable hPM hMsolv
    have hQs : Group.IsSolvable ↥Q := isSolvable_of_le_of_isSolvable hQM hMsolv
    have hcop : (Nat.card ↥P).Coprime (Nat.card ↥Q) := by
      rw [hPcard, hQ.2]
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp hq).2 hpq)
    exact (le_commutator_of_coprime_of_inf_centralizer_eq_bot hPnorm hcop hfix).trans
      (Subgroup.commutator_mono hQM hPM)
  have hAne : alphaCoreIn M ≠ ⊥ := by
    intro hbot
    have hcore : alphaCore ↥M = ⊥ := by
      have hb := hbot
      rw [alphaCoreIn, ← Subgroup.map_bot M.subtype] at hb
      exact Subgroup.map_injective M.subtype_injective hb
    have hα := alphaPrimes_eq_empty_of_alphaCore_eq_bot hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hM hcore
    have hnil := isNilpotent_commutator_of_alphaPrimes_eq_empty hoddM hα
    have hMle := le_normalizer_of_isNilpotent_commutator hq hnil hQC
      (natCard_eq_pow_factorization_commutator hq hQ.2 hQC)
    exact hnotuniq (isCoatom_ge_eq_singleton_of_normalizer_eq hM
      (normalizer_eq_of_isCoatom hM hQbot hQM hMle))
  have hqα : q ∉ alphaPrimes ↥M := by
    intro hqa
    have hrank : 3 ≤ elementaryAbelianPRank q ↥Q := by
      rw [elementaryAbelianPRank_eq_of_le_of_natCard_eq_pow_factorization hq hQM hQ.2]
      exact three_le_elementaryAbelianPRank_of_mem_alphaPrimes hqa
    exact hnotuniq (isCoatom_ge_eq_singleton_of_three_le_rank hG.not_isMulCommutative
      hG.odd_natCard hG.isSolvable_of_ne_top hM hQM
      (hrank.trans (elementaryAbelianPRank_le_maxElementaryAbelianPRank hq))
      Subgroup.le_normalizer hQnorm)
  have hqβ : q ∉ betaPrimes ↥M := fun h => hqα (betaPrimes_subset_alphaPrimes h)
  have hqodd : Odd q := hG.odd_natCard.of_dvd_nat
    ((prime_dvd_natCard_of_natCard_eq_pow hQ.2 hQbot).trans
      ((Subgroup.card_dvd_of_le hQM).trans M.card_subgroup_dvd_card))
  have hαβ : alphaPrimes ↥M = betaPrimes ↥M := by
    refine le_antisymm (fun r hr => ?_) betaPrimes_subset_alphaPrimes
    by_contra hrβ
    have hrp : r.Prime := prime_of_mem_alphaPrimes hr
    have hrq : r ≠ q := fun h => hqα (h ▸ hr)
    have hrodd : Odd r := hG.odd_natCard.of_dvd_nat
      ((Nat.dvd_of_mem_primeFactors (alphaPrimes_subset_primeFactors hr)).trans
        M.card_subgroup_dvd_card)
    obtain ⟨R, hRsyl, hRcomm⟩ := h₁ G hGMOS M hM r q hrp hq hrodd hqodd hrq hrβ hqβ Q
      ((Nat.card ↥M).factorization q) hQM hQ.2 (Or.inl hQC)
    have hRM : IsSylowSubgroupOf r R M := isSylowSubgroupOf_of_isSylowIn_sigmaCore
      hG.not_isMulCommutative hG.odd_natCard hG.isSolvable_of_ne_top hM hrp hr hRsyl
    have hrank : 3 ≤ elementaryAbelianPRank r ↥R := by
      rw [elementaryAbelianPRank_eq_of_le_of_natCard_eq_pow_factorization hrp hRM.1 hRM.2]
      exact three_le_elementaryAbelianPRank_of_mem_alphaPrimes hr
    have hRQ : ⁅R, Q⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hRcomm
    have hRcent : R ≤ centralizer (Q : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hRQ
    exact hnotuniq (isCoatom_ge_eq_singleton_of_three_le_rank hG.not_isMulCommutative
      hG.odd_natCard hG.isSolvable_of_ne_top hM hRM.1
      (hrank.trans (elementaryAbelianPRank_le_maxElementaryAbelianPRank hrp))
      (hRcent.trans (Subgroup.centralizer_le_normalizer _)) hQnorm)
  have hAB : alphaCoreIn M = betaCore M := alphaCoreIn_eq_betaCore_of_alphaPrimes_eq hαβ
  have hset : Prep08.IsRegularTauOneAlphaSetup M P Q p q :=
    { isCoatom_M := hM, mem_tau1 := hptau, prime_q := hq, q_ne := fun h => hpq h.symm
      q_notMem_alpha := hqα, le_P := hPM, natCard_P := hPcard, le_Q := hQM
      Q_ne_bot := hQbot, isPGroup_Q := hQpg, normalized := hPnorm, centralizer_eq := hfix
      not_unique := hnotuniq }
  have hAcoreOf : Prep08.alphaCoreOf M = alphaCoreIn M := rfl
  obtain ⟨hfix1, hfix2⟩ := inf_alphaCoreOf_centralizer_fixed_points hG.not_isMulCommutative
    hG.odd_natCard hG.isSolvable_of_ne_top hset (by rw [hAcoreOf]; exact hAne)
  rw [hAcoreOf, hAB] at hfix1 hfix2
  refine ⟨hαβ, hAB, by rw [← hAB]; exact hAne, hqβ, hfix1, ?_⟩
  rw [centralizer_coe_mul_coe]
  rw [centralizer_coe_sup, inf_comm (centralizer (Q : Set G))] at hfix2
  exact hfix2

end

end CFSG.FeitThompson.Proofs
