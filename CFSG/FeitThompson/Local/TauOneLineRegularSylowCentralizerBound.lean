module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.TauOnePrimeCentralizerInclusion
import CFSG.FeitThompson.Local.BetaCoreHallQuotient
import CFSG.FeitThompson.Local.MixedFittingCentralizerConstrained
import CFSG.FeitThompson.Local.PrimeFreeFactorizationFixedSubgroupTransport
import CFSG.FeitThompson.Local.NilpotentDerivedQuotientSylowNormalizer
import CFSG.FeitThompson.Local.BetaPrimesSigmaCompatibility
import CFSG.FeitThompson.Local.AlphaSigmaPrimeSeparation
import CFSG.FeitThompson.Local.BetaSubgroupNormalizerInMaximal
import CFSG.FeitThompson.Local.NormalComplementDerivedIntersection
import CFSG.FeitThompson.Local.NormalPlaneElementCentralizerIndex
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.CriticalRegularComplementFixedPoints
import CFSG.FeitThompson.Local.PrimeCentralizerComplementNoncentral
import CFSG.FeitThompson.Foundations.PiSubgroupInHallSolvable
import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.Local.GlobalMaximalPlaneGeometry
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup Pointwise

universe u

theorem map_subgroupOf_subgroupOfEquivOfLe {G : Type*} [Group G] {K H A : Subgroup G}
    (hHK : H ≤ K) :
    ((A.subgroupOf K).subgroupOf (H.subgroupOf K)).map
        (Subgroup.subgroupOfEquivOfLe hHK).toMonoidHom = A.subgroupOf H := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [Subgroup.subgroupOfEquivOfLe] using hx
  · intro hy
    refine ⟨(Subgroup.subgroupOfEquivOfLe hHK).symm y, ?_, by simp⟩
    simpa [Subgroup.mem_subgroupOf] using hy

theorem FBG_tau_one_fixed_core_transfer
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FTS_admissible_tau_one_prime_centralizer_inclusion.{u})
    (h₃ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FBG_tau_one_fixed_core_transfer.{u} := by
  intro G _ _ hG M L hM hL hnc p hp hpM hpL P hPML hPcard q hq hqp Q hQS hQne hPQ hQcent hQL r hr
    hrβL hrC
  have _i : Finite G := Finite.of_fintype G
  have _i2 := hG.isSimpleGroup
  have hsolvM : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hM.1
  have _i3 := hsolvM
  have hconj : ∀ g : G, MulAut.conj g • M ≠ L := by
    intro g hgl
    refine hnc g⁻¹ ?_
    rw [← hgl]
    simp [CFSG.FeitThompson.conjSubgroup, conj_smul_eq_map_conj]
  obtain ⟨-, -, hpσM, -, hpM'⟩ := mem_tau1Primes_iff.mp hpM
  obtain ⟨-, -, hpσL, -, -⟩ := mem_tau1Primes_iff.mp hpL
  have hrσL : r ∈ sigmaPrimes L :=
    betaPrimes_subset_sigmaPrimes hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hL hrβL
  have hpr : p ≠ r := fun h => hpσL (h ▸ hrσL)
  have hdisj := disjoint_sigmaPrimes_alphaPrimes_of_not_conj hG.not_isMulCommutative
    hG.odd_natCard hG.isSolvable_of_ne_top hM hL hconj
  have hrσM : r ∉ sigmaPrimes M := fun hrM =>
    Set.disjoint_left.mp hdisj hrM (betaPrimes_subset_alphaPrimes hrβL)
  have hrβM : r ∉ betaPrimes ↥M := fun h =>
    hrσM (betaPrimes_subset_sigmaPrimes hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hM h)
  have hrD : ¬ r ∣ Nat.card ↥(betaCore M) := fun hdvd =>
    hrβM (isPiSubgroup_iff.mp (isPiSubgroup_betaCore M) r
      (Nat.mem_primeFactors.2 ⟨hr, hdvd, Nat.card_pos.ne'⟩))
  obtain ⟨hHallM, -, hSM⟩ := h₁ G hG M hM
  have hHall : IsHallPiSubgroup (sigmaPrimes M) ((sigmaCore M).subgroupOf M) := hHallM.2
  have hG6 : _root_.CFSG.FeitThompson.Prep06.IsMinimalOddSimple G :=
    { odd := hG.odd_natCard
      simple := hG.isSimpleGroup
      nonabelian := hG.not_isMulCommutative
      solvable := hG.isSolvable_of_ne_top }
  have hQM : Q ≤ M := hQS.1
  have hQcard : Nat.card ↥Q = q ^ (Nat.card ↥M).factorization q := hQS.2
  have hPM : P ≤ M := hPML.trans inf_le_left
  have _i4 : Group.IsSolvable ↥P := isSolvable_of_le_of_isSolvable hPM hsolvM
  have _i5 : Group.IsSolvable ↥Q := isSolvable_of_le_of_isSolvable hQM hsolvM
  have hcopPQ : (Nat.card ↥P).Coprime (Nat.card ↥Q) := by
    rw [hPcard, hQcard]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp hq).2 (Ne.symm hqp))
  have hQcomm : Q ≤ (⁅M, M⁆ : Subgroup G) :=
    (le_commutator_of_coprime_of_inf_centralizer_eq_bot hPQ hcopPQ hQcent).trans
      (Subgroup.commutator_mono hQM hPM)
  have hBM' : betaCore M ≤ (⁅M, M⁆ : Subgroup G) := betaCore_le_commutator hG6 hM hSM
  have hNorm := normal_subgroupOf_betaCore_commutator hG6 hM hSM
  have _i6 := hNorm
  have hnil0 : Group.IsNilpotent
      (↥(⁅M, M⁆ : Subgroup G) ⧸ (betaCore M).subgroupOf (⁅M, M⁆ : Subgroup G)) :=
    Group.nilpotent_of_mulEquiv
      (_h := isNilpotent_quotient_piCore_commutator h₃ hG6 hM)
      (QuotientGroup.quotientMulEquivOfEq (subgroupOf_betaCore_commutator hG6 hM hSM).symm)
  have _i7 : ((betaCore M).subgroupOf M).Normal := betaCore_normal_subgroupOf M
  have _i8 : ((⁅M, M⁆ : Subgroup G).subgroupOf M).Normal :=
    CFSG.FeitThompson.normal_subgroupOf_commutator_self M
  have _i9 : (((betaCore M).subgroupOf M).subgroupOf
      ((⁅M, M⁆ : Subgroup G).subgroupOf M)).Normal :=
    Subgroup.Normal.subgroupOf _i7 _
  have hnil : Group.IsNilpotent (↥((⁅M, M⁆ : Subgroup G).subgroupOf M) ⧸
      ((betaCore M).subgroupOf M).subgroupOf ((⁅M, M⁆ : Subgroup G).subgroupOf M)) :=
    Group.nilpotent_of_mulEquiv (_h := hnil0)
      (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_self M))
        (map_subgroupOf_subgroupOfEquivOfLe (Subgroup.commutator_le_self M))).symm
  have hBL : (betaCore M).subgroupOf M ≤ (⁅M, M⁆ : Subgroup G).subgroupOf M :=
    Subgroup.comap_mono hBM'
  have hYL : Q.subgroupOf M ≤ (⁅M, M⁆ : Subgroup G).subgroupOf M := Subgroup.comap_mono hQcomm
  have hYcard : Nat.card ↥(Q.subgroupOf M)
      = q ^ (Nat.card ↥((⁅M, M⁆ : Subgroup G).subgroupOf M)).factorization q := by
    rw [natCard_subgroupOf_of_le hQM, natCard_subgroupOf_of_le (Subgroup.commutator_le_self M)]
    exact natCard_eq_pow_factorization_of_le_of_le hq hQcomm (Subgroup.commutator_le_self M) hQcard
  have hfrat : (betaCore M).subgroupOf M
      ⊔ normalizer ((Q.subgroupOf M : Subgroup ↥M) : Set ↥M) = ⊤ :=
    sup_normalizer_eq_top_of_isNilpotent_quotient hq hBL hnil hYL hYcard
  have hPmcard : Nat.card ↥(P.subgroupOf M) = p := by rw [natCard_subgroupOf_of_le hPM, hPcard]
  have hPmN : P.subgroupOf M ≤
      normalizer ((normalizer ((Q.subgroupOf M : Subgroup ↥M) : Set ↥M) : Subgroup ↥M) : Set ↥M) :=
    le_normalizer_normalizer_of_le (le_normalizer_subgroupOf hPQ)
  have hBcommM : (betaCore M).subgroupOf M ≤ _root_.commutator ↥M := by
    rw [commutator_eq_subgroupOf_commutator]; exact hBL
  have hpcommM : ¬ p ∣ Nat.card ↥(_root_.commutator ↥M) := by
    rw [commutator_eq_subgroupOf_commutator,
      natCard_subgroupOf_of_le (Subgroup.commutator_le_self M)]
    exact hpM'
  have hrDm : ¬ r ∣ Nat.card ↥((betaCore M).subgroupOf M) := by
    rw [natCard_subgroupOf_of_le (betaCore_le M)]; exact hrD
  have hrCm : r ∣ Nat.card ↥(centralizer ((P.subgroupOf M : Subgroup ↥M) : Set ↥M)) := by
    rw [centralizer_subgroupOf hPM, natCard_subgroupOf_of_le (inf_le_left)]
    exact hrC
  obtain ⟨R₀, hR₀le, hR₀card⟩ :=
    exists_le_inf_centralizer_natCard_eq (M := ↥M) hp hr hpr hPmcard hBcommM hPmN hfrat
      hpcommM hrDm hrCm
  have hR₀c : R₀ ≤ centralizer ((P.subgroupOf M : Subgroup ↥M) : Set ↥M) := hR₀le.trans inf_le_left
  have hR₀n : R₀ ≤ normalizer ((Q.subgroupOf M : Subgroup ↥M) : Set ↥M) := hR₀le.trans inf_le_right
  have hRcard : Nat.card ↥(R₀.map M.subtype) = r := by
    rw [Subgroup.card_map_of_injective M.subtype_injective, hR₀card]
  have hRM : R₀.map M.subtype ≤ M := Subgroup.map_subtype_le _
  have hRcent : R₀.map M.subtype ≤ M ⊓ centralizer (P : Set G) := by
    rw [centralizer_subgroupOf hPM] at hR₀c
    calc R₀.map M.subtype
        ≤ ((M ⊓ centralizer (P : Set G)).subgroupOf M).map M.subtype := Subgroup.map_mono hR₀c
      _ = M ⊓ centralizer (P : Set G) := Subgroup.map_subgroupOf_eq_of_le inf_le_left
  have hRQ : R₀.map M.subtype ≤ normalizer (Q : Set G) := by
    rintro y ⟨x, hx, rfl⟩
    exact mem_normalizer_of_mem_normalizer_subgroupOf hQM (hR₀n hx)
  have hRL : R₀.map M.subtype ≤ L := hRQ.trans hQL
  have hRne : R₀.map M.subtype ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hRcard
    exact hr.one_lt.ne hRcard
  have hNRL : normalizer ((R₀.map M.subtype : Subgroup G) : Set G) ≤ L :=
    normalizer_le_of_forall_mem_betaPrimes hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hL hRL hRne (by
        intro s hs hsdvd
        rw [hRcard] at hsdvd
        rwa [(Nat.prime_dvd_prime_iff_eq hs hr).1 hsdvd])
  have hRcentP : R₀.map M.subtype ≤ centralizer (P : Set G) := hRcent.trans inf_le_right
  have hRnormP : R₀.map M.subtype ≤ normalizer (P : Set G) :=
    hRcentP.trans (Subgroup.centralizer_le_normalizer _)
  have hcoeSup : ((P ⊔ R₀.map M.subtype : Subgroup G) : Set G)
      = (P : Set G) * ((R₀.map M.subtype : Subgroup G) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left P _ hRnormP
  have hcardPR : Nat.card ↥(P ⊔ R₀.map M.subtype : Subgroup G) ∣ p * r := by
    have h := natCard_mul_mul_natCard_inf P (R₀.map M.subtype)
    rw [← hcoeSup, hPcard, hRcard] at h
    exact ⟨Nat.card ↥(P ⊓ R₀.map M.subtype : Subgroup G), h.symm⟩
  have hPRle : (P ⊔ R₀.map M.subtype : Subgroup G) ≤ M := sup_le hPM hRM
  have hPRpi : IsPiSubgroup ((sigmaPrimes M)ᶜ)
      ((P ⊔ R₀.map M.subtype : Subgroup G).subgroupOf M) := by
    refine isPiSubgroup_iff.2 fun s hs => ?_
    rw [natCard_subgroupOf_of_le hPRle] at hs
    have hsp := Nat.prime_of_mem_primeFactors hs
    have hsd : s ∣ p * r := (Nat.dvd_of_mem_primeFactors hs).trans hcardPR
    rcases (Nat.Prime.dvd_mul hsp).1 hsd with h | h
    · rw [Set.mem_compl_iff, (Nat.prime_dvd_prime_iff_eq hsp hp).1 h]; exact hpσM
    · rw [Set.mem_compl_iff, (Nat.prime_dvd_prime_iff_eq hsp hr).1 h]; exact hrσM
  obtain ⟨E₀, hE₀Hall, hWE₀⟩ := exists_isHallSubgroup_ge_of_isPiSubgroup (G := ↥M) hPRpi
  have hsmap : ((sigmaCore M).subgroupOf M).map M.subtype = sigmaCore M :=
    Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le M)
  have hscard : IsPiNumber (sigmaPrimes M) (Nat.card ↥((sigmaCore M).subgroupOf M)) :=
    isPiSubgroup_iff_isPiNumber.1 hHall.isPiSubgroup
  have hsindex : IsPiNumber ((sigmaPrimes M)ᶜ) ((sigmaCore M).subgroupOf M).index :=
    isPiNumber_iff.2 fun t ht => hHall.notMem_of_mem_primeFactors_index t ht
  have hcop1 : (Nat.card ↥((sigmaCore M).subgroupOf M)).Coprime (Nat.card ↥E₀) :=
    hscard.coprime_of_compl hE₀Hall.natCard Nat.card_pos.ne' Nat.card_pos.ne'
  have hcop2 : ((sigmaCore M).subgroupOf M).index.Coprime E₀.index :=
    hsindex.coprime_of_compl hE₀Hall.index Subgroup.index_ne_zero_of_finite
      Subgroup.index_ne_zero_of_finite
  have hprod : Nat.card ↥E₀ * E₀.index
      = Nat.card ↥((sigmaCore M).subgroupOf M) * ((sigmaCore M).subgroupOf M).index := by
    rw [Subgroup.card_mul_index, Subgroup.card_mul_index]
  have hTdvd : Nat.card ↥E₀ ∣ ((sigmaCore M).subgroupOf M).index :=
    hcop1.symm.dvd_of_dvd_mul_left ⟨E₀.index, hprod.symm⟩
  have hidvd : ((sigmaCore M).subgroupOf M).index ∣ Nat.card ↥E₀ :=
    hcop2.dvd_of_dvd_mul_right ⟨Nat.card ↥((sigmaCore M).subgroupOf M),
      by rw [hprod, Nat.mul_comm]⟩
  have hTeq : Nat.card ↥E₀ = ((sigmaCore M).subgroupOf M).index := Nat.dvd_antisymm hTdvd hidvd
  have hcardprod : Nat.card ↥((sigmaCore M).subgroupOf M) * Nat.card ↥E₀ = Nat.card ↥M := by
    rw [hTeq]; exact Subgroup.card_mul_index _
  have hdisj2 : Disjoint ((sigmaCore M).subgroupOf M) E₀ :=
    Subgroup.disjoint_of_coprime_natCard hcop1
  have hsup : (sigmaCore M).subgroupOf M ⊔ E₀ = ⊤ :=
    (Subgroup.isComplement'_of_card_mul_and_disjoint hcardprod hdisj2).sup_eq_top
  have hEM : E₀.map M.subtype ≤ M := Subgroup.map_subtype_le _
  have hsd : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) (E₀.map M.subtype) := by
    refine ⟨?_, le_normalizer_sigmaCore M, ?_⟩
    · calc sigmaCore M ⊔ E₀.map M.subtype
          = (((sigmaCore M).subgroupOf M) ⊔ E₀).map M.subtype := by rw [Subgroup.map_sup, hsmap]
        _ = M := by rw [hsup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    · rw [disjoint_iff, ← hsmap, ← Subgroup.map_inf _ _ _ M.subtype_injective,
        disjoint_iff.1 hdisj2, Subgroup.map_bot]
  have hPE : P ≤ E₀.map M.subtype := by
    calc P = (P.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hPM).symm
      _ ≤ E₀.map M.subtype :=
          Subgroup.map_mono ((Subgroup.comap_mono (le_sup_left : P ≤ _)).trans hWE₀)
  have hRE : R₀.map M.subtype ≤ E₀.map M.subtype := by
    calc R₀.map M.subtype
        = ((R₀.map M.subtype).subgroupOf M).map M.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hRM).symm
      _ ≤ E₀.map M.subtype :=
          Subgroup.map_mono ((Subgroup.comap_mono (le_sup_right : R₀.map M.subtype ≤ _)).trans hWE₀)
  have hG9 : CFSG.FeitThompson.Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hkey := FTS_tau_one_prime_centralizer_inclusion h₂ G hG9 M hM (E₀.map M.subtype) hEM hsd
    p r hp hr hpM P hPE hPcard (R₀.map M.subtype) (le_inf hRE hRcentP) hRcard
  intro x hx
  have hx' : x ∈ sigmaCore M ⊓ centralizer ((R₀.map M.subtype : Subgroup G) : Set G) := hkey hx
  exact hNRL (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.1 hx').2)

end

end CFSG.FeitThompson.Proofs
