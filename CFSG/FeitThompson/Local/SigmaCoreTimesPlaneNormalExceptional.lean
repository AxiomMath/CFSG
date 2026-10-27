module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.InvariantSylowOutsideSigmaCentralizedByPlane
import CFSG.FeitThompson.Local.ExceptionalPlaneFixedFreeLines
import CFSG.FeitThompson.Local.ExceptionalSylowAbelian
import CFSG.FeitThompson.Local.KappaResidualContainingComplementFitting
import CFSG.FeitThompson.Local.KappaResidualInPrescribedComplement
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerCommonFactor
import CFSG.FeitThompson.Local.OutsideSigmaPlanePrimesTauOneOrTwo
import CFSG.FeitThompson.Local.SigmaComplementThreeHallFactors
import CFSG.FeitThompson.Local.LowRankCharacteristicPrimeCutoffHall
import CFSG.FeitThompson.Local.HallCutoffPrimeTorsionNormal
import CFSG.FeitThompson.Local.OvergroupJoinsInvariantPrimeSubgroups
import CFSG.FeitThompson.Local.QuotientFittingInvariantComplement
import CFSG.FeitThompson.Local.RegularTauAlphaFixedPoints
import CFSG.FeitThompson.Local.FittingSplitsNormalHall
import CFSG.FeitThompson.Representations.ChiefActionKernelNormalQuotientLayers
import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
import CFSG.FeitThompson.Foundations.SolvableHallExistence
import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
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
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson
open Subgroup

universe u

variable {G : Type*} [Group G]

theorem eq_of_le_of_forall_prime_pow_dvd [Finite G] {C D : Subgroup G} (hCD : C ≤ D)
    (h : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥D → q ^ (Nat.card ↥D).factorization q ∣ Nat.card ↥C) :
    C = D := by
  have hfac : (Nat.card ↥D).factorization ≤ (Nat.card ↥C).factorization := by
    refine Finsupp.le_def.2 fun q => ?_
    rcases Nat.eq_zero_or_pos ((Nat.card ↥D).factorization q) with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    have hq : q ∈ (Nat.card ↥D).primeFactors := by
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.2 (by omega)
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    exact (hqp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1
      (h q hqp (Nat.dvd_of_mem_primeFactors hq))
  exact Subgroup.eq_of_le_of_card_ge hCD
    (Nat.le_of_dvd Nat.card_pos ((Nat.factorization_le_iff_dvd Nat.card_pos.ne'
      Nat.card_pos.ne').1 hfac))

theorem commutator_eq_bot_of_forall_invariant_sylow [Finite G] {K A : Subgroup G} [K.Normal]
    (hsolv : Group.IsSolvable ↥(K ⊔ A)) (hcop : (Nat.card ↥K).Coprime (Nat.card ↥A))
    (hcent : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥K → ∀ Q : Subgroup G, Q ≤ K →
      Nat.card ↥Q = q ^ (Nat.card ↥K).factorization q → A ≤ normalizer (Q : Set G) →
      ⁅Q, A⁆ = ⊥) :
    ⁅K, A⁆ = ⊥ := by
  have hAK : A ≤ normalizer (K : Set G) := Subgroup.le_normalizer_of_normal
  have hbotnorm : A ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    intro x _
    rw [mem_normalizer_iff]
    intro y
    simp [Subgroup.mem_bot]
  have hKC : K ⊓ centralizer (A : Set G) = K := by
    refine eq_of_le_of_forall_prime_pow_dvd inf_le_left fun q hq hqK => ?_
    obtain ⟨Q, hQK, hQHall, -, hAQ⟩ :=
      exists_isHallSubgroup_subgroupOf_ge_le_normalizer_of_le_normalizer hsolv hAK hcop
        ({q} : Set ℕ) (bot_le : (⊥ : Subgroup G) ≤ K)
        (by rw [Subgroup.card_bot]; exact isPiNumber_one) hbotnorm
    have hQcard : Nat.card ↥Q = q ^ (Nat.card ↥K).factorization q :=
      natCard_eq_pow_factorization_of_isHallSubgroup_singleton hq hQK hQHall
    exact hQcard ▸ Subgroup.card_dvd_of_le
      (le_inf hQK (Subgroup.commutator_eq_bot_iff_le_centralizer.1
        (hcent q hq hqK Q hQK hQcard hAQ)))
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hKC ▸ inf_le_right)

theorem commutator_subgroupOf_eq_bot_of_map {E : Subgroup G} {Q : Subgroup ↥E} {A : Subgroup G}
    (h : ⁅Q.map E.subtype, A⁆ = ⊥) : ⁅Q, A.subgroupOf E⁆ = ⊥ := by
  have hQ : Q.map E.subtype ≤ centralizer (A : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
  refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun x hx => ?_
  rw [mem_centralizer_iff]
  intro y hy
  exact Subtype.ext ((mem_centralizer_iff.1 (hQ (Subgroup.mem_map_of_mem _ hx))) (y : G)
    (Subgroup.mem_subgroupOf.1 hy))

theorem normal_subgroupOf_sigmaCore_sup [Finite G] {M A E : Subgroup G}
    (hsd : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E) (hEM : E ≤ M)
    (hEA : E ≤ normalizer (A : Set G)) : ((sigmaCore M ⊔ A).subgroupOf M).Normal := by
  refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
  have hS : sigmaCore M ≤ normalizer ((sigmaCore M ⊔ A : Subgroup G) : Set G) :=
    le_sup_left.trans Subgroup.le_normalizer
  have hE : E ≤ normalizer ((sigmaCore M ⊔ A : Subgroup G) : Set G) :=
    le_normalizer_sup (hEM.trans (le_normalizer_sigmaCore M)) hEA
  have h := sup_le hS hE
  rwa [hsd.sup_eq] at h

theorem FTS_exceptional_normal_plane_product
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₃ : Statements.FPL_low_rank_sylow_central_product.{u})
    (h₄ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_exceptional_normal_plane_product.{u} := by
  intro G _ _ hG p M A₀ A P hc
  have hsimple := hG.isSimpleGroup
  have : Fintype G := Fintype.ofFinite G
  have hp : p.Prime := hc.prime
  have hfp := Fact.mk hp
  have hM : IsCoatom M := hc.isCoatom
  have hAP : A ≤ P := hc.le_of_A
  have hPM : P ≤ M := hc.le_of_P
  have hAM : A ≤ M := hAP.trans hPM
  have hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p := hc.isSylowSubgroupOf.2
  have hAcard : Nat.card ↥A = p ^ 2 := hc.isElementaryAbelianPlane.natCard hp.ne_zero
  have hMin : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hsolvM : Group.IsSolvable ↥M := hG.isSolvable M hM.1
  obtain ⟨hHallM, -, -⟩ := h₁ G hMin M hM
  obtain ⟨E, hEM, hsd, hPE⟩ :=
    exists_isInternalSemidirectProduct_sigmaCore_ge_of_isHallPiSubgroupOf hHallM hsolvM hPM
      (fun r hr hrP => by
        have hrp : r = p := by
          rw [hPcard] at hrP
          exact (Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow hrP)
        exact hrp ▸ hc.notMem_sigmaPrimes)
  have hAE : A ≤ E := hAP.trans hPE
  have hEne : E ≠ ⊤ := fun h => hM.1 (top_le_iff.1 (h ▸ hEM))
  have hsolvE : Group.IsSolvable ↥E := hG.isSolvable E hEne
  have hoddE : Odd (Nat.card ↥E) := hG.odd_natCard.of_dvd_nat (Subgroup.card_subgroup_dvd_card E)
  have hHallE : IsHallSubgroup ((sigmaPrimes M)ᶜ) (E.subgroupOf M) :=
    isHallSubgroup_subgroupOf_of_isInternalSemidirectProduct
      (isHallSubgroup_iff_isHallPiSubgroup.2 hHallM.2) hsd
  have hfacME : ∀ r : ℕ, r.Prime → r ∉ sigmaPrimes M →
      (Nat.card ↥M).factorization r = (Nat.card ↥E).factorization r := by
    intro r hr hrσ
    rw [factorization_natCard_eq_of_isHallSubgroup hHallE hr hrσ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv]
  have hEσ : ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥E → r ∉ sigmaPrimes M := fun r hr hrE =>
    notMem_sigmaPrimes_of_dvd_natCard_complement hHallM.2 hsd hr hrE
  have hrankE : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(fittingRaw ↥E) ≤ 2 := by
    intro q hq
    refine le_trans (elementaryAbelianPRank_subgroup_le hq.one_lt _) ?_
    by_contra hlt
    have h3 : 3 ≤ elementaryAbelianPRank q ↥E := by omega
    obtain ⟨H, ⟨e⟩⟩ := mem_elementaryAbelianRanks.1 ((le_elementaryAbelianPRank_iff hq.one_lt).1 h3)
    have : NeZero q := ⟨hq.ne_zero⟩
    have hHcard : Nat.card ↥H = q ^ 3 := by rw [Nat.card_congr e.toEquiv]; simp
    have hqE : q ∣ Nat.card ↥E :=
      dvd_trans (by rw [hHcard]; exact dvd_pow_self q (by norm_num))
        (Subgroup.card_subgroup_dvd_card H)
    have h2 : elementaryAbelianPRank q ↥M ≤ 2 :=
      elementaryAbelianPRank_le_two_of_notMem_sigmaPrimes hG.not_isMulCommutative hG.odd_natCard
        hG.isSolvable hM hq (hEσ q hq hqE)
    have h4 := elementaryAbelianPRank_le_of_le (X := G) hq.one_lt hEM
    omega
  have hPab : IsMulCommutative ↥P := (FTS_exceptional_sylow_abelian h₁ h₃ h₄ G hG p M A₀ A P hc).1
  obtain ⟨hAset, -, -⟩ := FTS_exceptional_plane_fixed_free_lines h₁ h₃ h₄ G hG p M A₀ A P hc
  obtain ⟨hKchar, hKHall, -, -, hKP⟩ :=
    piCore_primesGT_primesGE_isCharacteristicHall_and_sup_sylow (E := ↥E) hp hoddE hrankE
  have hPEcard : Nat.card ↥(P.subgroupOf E) = p ^ (Nat.card ↥E).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPE).toEquiv, hPcard,
      hfacME p hp hc.notMem_sigmaPrimes]
  set S : Sylow p ↥E := Sylow.ofCard (P.subgroupOf E) hPEcard with hSdef
  have hScoe : (S : Subgroup ↥E) = P.subgroupOf E := Sylow.coe_ofCard _ _
  have hSab : IsMulCommutative ↥(S : Subgroup ↥E) := by
    rw [hScoe]
    exact isMulCommutative_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hPE)
  set K : Subgroup ↥E := piCore (primesGT p) ↥E with hKdef
  have hKnormal : K.Normal := Subgroup.normal_of_characteristic K
  have hKgt : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥K → p < q := fun q hq hqK =>
    (mem_primesGT.1 (isPiNumber_iff.1 hKHall.natCard q
      (Nat.mem_primeFactors.2 ⟨hq, hqK, Nat.card_pos.ne'⟩))).2
  have hKp : ¬ p ∣ Nat.card ↥K := fun hdvd => absurd (hKgt p hp hdvd) (lt_irrefl p)
  have hLnormal : (K ⊔ (S : Subgroup ↥E)).Normal := by
    rw [← hKP S]
    exact Subgroup.normal_of_characteristic _
  have hAeq : A.subgroupOf E = powEqOneSubgroup p (S : Subgroup ↥E) := by
    ext x
    have hxA : (x : ↥E) ∈ A.subgroupOf E ↔ (x : G) ∈ (A : Set G) := Subgroup.mem_subgroupOf
    rw [hxA, hAset, mem_powEqOneSubgroup, hScoe, Subgroup.mem_subgroupOf]
    refine ⟨fun hx => ⟨hx.1, Subtype.ext (by simpa using hx.2)⟩, fun hx => ⟨hx.1, ?_⟩⟩
    have h := congrArg (fun z : ↥E => (z : G)) hx.2
    simpa using h
  have hAcardE : Nat.card ↥(A.subgroupOf E) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAE).toEquiv, hAcard]
  have hKA : ⁅K, A.subgroupOf E⁆ = ⊥ := by
    refine commutator_eq_bot_of_forall_invariant_sylow inferInstance ?_ ?_
    · rw [hAcardE]
      exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hKp).symm
    · intro q hq hqK Q hQK hQcard hAQ
      refine commutator_subgroupOf_eq_bot_of_map ?_
      set Q' : Subgroup G := Q.map E.subtype with hQ'def
      have hQ'E : Q' ≤ E := map_subtype_le _
      have hQ'M : Q' ≤ M := hQ'E.trans hEM
      have hQ'card : Nat.card ↥Q' = Nat.card ↥Q := Subgroup.card_subtype E Q
      have hqE : q ∣ Nat.card ↥E := hqK.trans (Subgroup.card_subgroup_dvd_card K)
      have hqσ : q ∉ sigmaPrimes M := hEσ q hq hqE
      have hqp : q ≠ p := (hKgt q hq hqK).ne'
      have hfacKE : (Nat.card ↥K).factorization q = (Nat.card ↥E).factorization q :=
        (factorization_natCard_eq_of_isHallSubgroup hKHall hq
          (mem_primesGT.2 ⟨hq, hKgt q hq hqK⟩)).symm
      have hQ'sylow :
          _root_.CFSG.FeitThompson.IsSylowSubgroupOf q Q' M := by
        refine ⟨hQ'M, ?_⟩
        rw [hQ'card, hQcard, hfacKE, ← hfacME q hq hqσ]
      have hAQ' : A ≤ normalizer ((Q' : Subgroup G) : Set G) := by
        have h := le_normalizer_map_subtype (E := E) hAQ
        rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hAE] at h
      exact FTS_exceptional_plane_centralizes_outside_sylow h₁ h₂ h₃ h₄ G hG p M A₀ A P hc q hq hqp
        hqσ Q' hQ'sylow hAQ'
  have hAnormalE : (A.subgroupOf E).Normal := by
    rw [hAeq]
    exact powEqOneSubgroup_sylow_normal hp S ((Nat.Prime.coprime_iff_not_dvd hp).2 hKp).symm
      hLnormal (hAeq ▸ hKA)
  have hEA : E ≤ normalizer (A : Set G) :=
    have := hAnormalE
    Subgroup.le_normalizer_of_normal_subgroupOf hAE
  exact normal_subgroupOf_sigmaCore_sup hsd hEM hEA

end

end CFSG.FeitThompson.Proofs
