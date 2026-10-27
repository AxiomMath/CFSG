module

public import Mathlib
public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.KappaPositiveMultipleCoreTrivialResidual
import CFSG.FeitThompson.Local.HallKappaSubgroupTI
import CFSG.FeitThompson.OddOrder.PSubgroupInSigmaCoreOfMaximal
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived
import CFSG.FeitThompson.Local.KappaPrimeLineFixedEquivalence
import CFSG.FeitThompson.Local.NonuniqueScnAuxiliaryPrime
import CFSG.FeitThompson.Local.PComplementQuotientSylowRank
import CFSG.FeitThompson.Local.FreeActionKernelGrowthProperInvariant
import CFSG.FeitThompson.Local.PrimeFreeFactorizationFixedSubgroupTransport
import CFSG.FeitThompson.Local.BetaPrimesSigmaCompatibility
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.SigmaCoreConjugation
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy
import CFSG.FeitThompson.Foundations.PiSubgroupInHallSolvable
import CFSG.FeitThompson.Representations.NoInducedIrreducibleFixedOrbitOrder
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup Pointwise
open CFSG.FeitThompson

universe u

variable {G : Type u} [Group G]

theorem exists_isHallPiSubgroupOf_ge [Finite G] {π : Set ℕ} {M Q : Subgroup G}
    (hsolv : Group.IsSolvable ↥M) (hQM : Q ≤ M) (hQ : IsPiSubgroup π Q) :
    ∃ K : Subgroup G, IsHallPiSubgroupOf π K M ∧ Q ≤ K := by
  have hcard : Nat.card ↥(Q.subgroupOf M) = Nat.card ↥Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv
  have hpi : IsPiNumber π (Nat.card ↥(Q.subgroupOf M)) := by
    rw [hcard]; exact isPiSubgroup_iff_isPiNumber.1 hQ
  obtain ⟨H, hH, hQH⟩ := exists_isHallSubgroup_ge (π := π) (G := ↥M) hpi
  refine ⟨H.map M.subtype, ⟨Subgroup.map_subtype_le _, ?_⟩, ?_⟩
  · have hmap : (H.map M.subtype).subgroupOf M = H :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective H
    rw [hmap]
    exact hH.isHallPiSubgroup
  · intro y hy
    have hmem : y ∈ (Q.subgroupOf M).map M.subtype := by
      rw [Subgroup.subgroupOf_map_subtype]
      exact ⟨hy, hQM hy⟩
    exact Subgroup.map_mono hQH hmem

theorem factorization_eq_of_isHallPiOf [Finite G] {π : Set ℕ} {A X : Subgroup G}
    (hA : Prep03.IsHallPiOf π A X) {p : ℕ} (hp : p.Prime) (hpπ : p ∈ π) :
    (Nat.card ↥A).factorization p = (Nat.card ↥X).factorization p := by
  have hmul : Nat.card ↥A * A.relIndex X = Nat.card ↥X := natCard_mul_relIndex hA.1
  have hAne : Nat.card ↥A ≠ 0 := Nat.card_pos.ne'
  have hIne : A.relIndex X ≠ 0 := by
    intro h0
    rw [h0, Nat.mul_zero] at hmul
    exact Nat.card_pos.ne' hmul.symm
  have hidx : ¬ p ∣ A.relIndex X := fun h =>
    hA.2.2 p (Nat.mem_primeFactors.2 ⟨hp, h, hIne⟩) hpπ
  rw [← hmul, Nat.factorization_mul hAne hIne]
  simp [Nat.factorization_eq_zero_of_not_dvd hidx]

theorem elementaryAbelianPRank_eq_one_of_isCyclic_isHallPiOf [Finite G] {π : Set ℕ}
    {A X : Subgroup G} (hA : Prep03.IsHallPiOf π A X) (hcyc : IsCyclic ↥A)
    {p : ℕ} (hp : p.Prime) (hpπ : p ∈ π) (hpX : p ∣ Nat.card ↥X) :
    elementaryAbelianPRank p ↥X = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p ↥A))
  set P : Subgroup G := (S : Subgroup ↥A).map A.subtype with hPdef
  have hPcard : Nat.card ↥P = p ^ (Nat.card ↥X).factorization p := by
    rw [hPdef, Subgroup.card_subtype, S.card_eq_multiplicity,
      factorization_eq_of_isHallPiOf hA hp hpπ]
  have hPA : P ≤ A := Subgroup.map_subtype_le _
  have hPX : P ≤ X := hPA.trans hA.1
  have hPcyc : IsCyclic ↥P := isCyclic_of_le hPA
  refine elementaryAbelianPRank_eq_one_of_isCyclic_sylow hp hpX ⟨?_, ?_⟩
  · refine Sylow.ofCard (P.subgroupOf X) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPX).toEquiv, hPcard]
  · rw [Sylow.coe_ofCard, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPX]
    exact hPcyc

theorem FTS_kappa_positive_support_sigma_primes_disjoint
    (h₁ : Statements.FBG_kappa_nontrivial_complement_structure.{u})
    (h₂ : Statements.FNI_kappa_local_pair.{u})
    (h₃ : Statements.FNI_kappa_pair_hall_intersection.{u})
    (h₄ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₅ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₆ : Statements.FTS_beta_or_derived_line_centralizer_unique.{u})
    (h₇ : Statements.FTS_signalizer_unique_supporting_maximum.{u}) :
    Statements.FTS_kappa_positive_support_sigma_primes_disjoint.{u} := by
  intro G _ _ hG x hx hk M hM T hT hTu hκ q hqM hqT
  have hsimple := hG.isSimpleGroup
  have hodd := hG.odd_natCard
  have hna := hG.not_isMulCommutative
  have hsolv := hG.isSolvable
  have hMc : IsCoatom M := (CFSG.FeitThompson.mem_sigmaSupportingMaximals.1 hM).1
  have hTc : IsCoatom T := CFSG.FeitThompson.mem_maximalSubgroups.1 hT
  have hq : q.Prime := prime_of_mem_sigmaPrimes hqT
  have _ifact : Fact q.Prime := ⟨hq⟩
  have _ift : Fintype G := Fintype.ofFinite G
  have h7 := (h₇ G ⟨hodd, hsimple, hna, hsolv⟩ x hx hk).2 T hTc hTu.le
  have h7M := h7.2.2.2 M hM
  have hqσM : q ∉ sigmaPrimes M := fun h => by
    have hmem : q ∈ sigmaPrimes T ∩ sigmaPrimes M := ⟨hqT, h⟩
    rw [h7M.2.2.2.1] at hmem; exact hmem
  have hqβT : q ∈ betaPrimes ↥T := h7M.2.2.2.2.2 q hqT hqM
  obtain ⟨⟨p, -, hpσM, hpτT, -, -⟩, -, hresidual⟩ :=
    FTS_kappa_positive_multiple_core_trivial_residual h₁ h₄ h₅ h₇ G hG x hx hk M hM T hT hTu hκ
  have hp : p.Prime := prime_of_mem_tauTwoPrimes hpτT
  have hpT2 : elementaryAbelianPRank p ↥T = 2 := (mem_tauTwoPrimes_iff.1 hpτT).2.2
  have hsolvM : Group.IsSolvable ↥M := hsolv M hMc.1
  have hqκ : q ∈ kappaPrimes M := by
    obtain ⟨K₀, hK₀, -⟩ := exists_isHallPiSubgroupOf_ge (π := kappaPrimes M) (Q := ⊥)
      hsolvM bot_le (by rw [isPiSubgroup_iff]; simp)
    have hcard : Nat.card ↥M = Nat.card ↥(sigmaCore M) * Nat.card ↥K₀ :=
      (hresidual K₀ hK₀).natCard_eq_mul
    have hqS : ¬ q ∣ Nat.card ↥(sigmaCore M) := fun h =>
      hqσM (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) q
        (Nat.mem_primeFactors.2 ⟨hq, h, Nat.card_pos.ne'⟩))
    have hqK : q ∣ Nat.card ↥K₀ := by
      rw [hcard] at hqM
      exact ((Nat.Prime.dvd_mul hq).1 hqM).resolve_left hqS
    exact isPiSubgroup_iff.1 hK₀.isPiSubgroup q
      (Nat.mem_primeFactors.2 ⟨hq, hqK, Nat.card_pos.ne'⟩)
  obtain ⟨y, hyM, hyord⟩ := exists_mem_orderOf_eq_of_dvd hq hqM
  set Q : Subgroup G := zpowers y with hQdef
  have hQM : Q ≤ M := zpowers_le.2 hyM
  have hQcard : Nat.card ↥Q = q := by rw [hQdef, Nat.card_zpowers, hyord]
  have hQp : IsPGroup q ↥Q := IsPGroup.of_card (n := 1) (by rw [hQcard]; ring)
  obtain ⟨K, hK, hQK⟩ := exists_isHallPiSubgroupOf_ge (π := kappaPrimes M) hsolvM hQM
    (by rw [isPiSubgroup_iff, hQcard, hq.primeFactors]; simpa using hqκ)
  have hidxT : ¬ q ∣ (sigmaCore T).index := fun h =>
    isPiNumber_compl_iff.1 (isHallSubgroup_sigmaCore hna hodd hsolv hTc).index q
      (Nat.mem_primeFactors.2 ⟨hq, h, Subgroup.index_ne_zero_of_finite⟩) hqT
  obtain ⟨Q₁, hQ₁le, hQ₁card⟩ := exists_le_natCard_eq_pow_factorization_of_not_dvd_index hq hidxT
  obtain ⟨g, hg⟩ := exists_le_conj_smul_of_isPGroup hQ₁card hQp
  set L : Subgroup G := MulAut.conj g • T with hLdef
  have hQL : Q ≤ L :=
    hg.trans (Subgroup.pointwise_smul_le_pointwise_smul_iff.2 (hQ₁le.trans (sigmaCore_le T)))
  have hLc : IsCoatom L := isCoatom_conj_smul hTc g
  have hqβL : q ∈ betaPrimes ↥L := by rw [hLdef, betaPrimes_conj_smul]; exact hqβT
  have hcentL : centralizer (Q : Set G) ≤ L :=
    (h₆ G ⟨hodd, hsimple, hna, hsolv⟩ L Q hLc q hq hQL hQcard (Or.inl hqβL)).1.le
  set A : Subgroup G := Prep03.cent (sigmaCore M) (K : Set G) with hAdef
  set Z : Subgroup G := K ⊔ A with hZdef
  have hsetup : Prep03.IsKappaSetup G M K A Z :=
    { ambient := ⟨hodd, hsimple, hna, hsolv⟩
      isCoatom := hMc
      kappa_nonempty := hκ
      isHall_K := isHallPiOf_of_isHallPiSubgroupOf hK
      A_eq := rfl
      Z_eq := rfl }
  obtain ⟨Mstar, hMs1, hMs2, -, -, -, -, -, hZcyc, -, -, hprime, -⟩ := h₂ G M K A Z hsetup
  have hLMs : L = Mstar := (hprime Q hQK (by rw [hQcard]; exact hq)).2.2.2 L hLc hcentL
  have hAhall : Prep03.IsHallPiOf (sigmaPrimes M) A Mstar :=
    (h₃ G M K A Z Mstar hsetup hMs1.1 hMs1.2 hMs2).1
  have hAcyc : IsCyclic ↥A := isCyclic_of_le (le_sup_right : A ≤ Z)
  have hpL2 : elementaryAbelianPRank p ↥L = 2 := by
    rw [hLdef, elementaryAbelianPRank_conj_smul hp.one_lt]; exact hpT2
  have hpLdvd : p ∣ Nat.card ↥L :=
    (one_le_elementaryAbelianPRank_iff hp).1 (by rw [hpL2]; norm_num)
  have hpL1 : elementaryAbelianPRank p ↥L = 1 := by
    rw [hLMs] at hpLdvd ⊢
    exact elementaryAbelianPRank_eq_one_of_isCyclic_isHallPiOf hAhall hAcyc hp hpσM hpLdvd
  rw [hpL1] at hpL2
  exact absurd hpL2 (by norm_num)

end

end CFSG.FeitThompson.Proofs
