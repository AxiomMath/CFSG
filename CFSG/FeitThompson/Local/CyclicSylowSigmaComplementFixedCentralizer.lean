module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson

universe u

theorem FTS_cyclic_sylow_complement_fixed_centralizer
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_three_prime_normalizer_transfer.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_cyclic_sylow_complement_fixed_centralizer.{u} := by
  intro G _ _ hG M hM E hEM hsd p hp P hP hPne hPcyc X hXP hXne
  have hsimple := hG.isSimpleGroup
  have hMcoatom : IsCoatom M := hM
  have hGmin : CFSG.FeitThompson.Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  obtain ⟨hHallOf, hHallG, -⟩ :=
    haveI : Fintype G := Fintype.ofFinite G
    h₁ G ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩ M hMcoatom
  have hPE : P ≤ E := hP.1
  have hPM : P ≤ M := hPE.trans hEM
  have hcardP : Nat.card ↥P = p ^ (Nat.card ↥E).factorization p := hP.2
  have hXne1 : Nat.card ↥X ≠ 1 := fun h => hXne (Subgroup.card_eq_one.1 h)
  have hpX : p ∣ Nat.card ↥X := by
    have hq := Nat.minFac_prime hXne1
    have hqd : (Nat.card ↥X).minFac ∣ p ^ (Nat.card ↥E).factorization p :=
      (Nat.minFac_dvd _).trans (hcardP ▸ Subgroup.card_dvd_of_le hXP)
    have hqp : (Nat.card ↥X).minFac = p :=
      (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hqd)
    exact hqp ▸ Nat.minFac_dvd _
  have hpE : p ∣ Nat.card ↥E := hpX.trans (Subgroup.card_dvd_of_le (hXP.trans hPE))
  have hpM : p ∣ Nat.card ↥M := hpE.trans (Subgroup.card_dvd_of_le hEM)
  have hpσ : p ∉ sigmaPrimes M := by
    have h := hHallOf.2.notMem_of_mem_primeFactors_index
    rw [index_subgroupOf_left_eq hsd] at h
    exact h p (Nat.mem_primeFactors.2 ⟨hp, hpE, Nat.card_pos.ne'⟩)
  have hnotdvdS : ¬ p ∣ Nat.card ↥(sigmaCore M) := fun hd =>
    hpσ (isPiSubgroup_iff.1 hHallG.isPiSubgroup p
      (Nat.mem_primeFactors.2 ⟨hp, hd, Nat.card_pos.ne'⟩))
  have hcardM : Nat.card ↥M = Nat.card ↥(sigmaCore M) * Nat.card ↥E := hsd.natCard_eq_mul
  have hfac : (Nat.card ↥P).factorization p = (Nat.card ↥M).factorization p := by
    rw [hcardP, hcardM, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnotdvdS, zero_add, hp.factorization_pow,
      Finsupp.single_eq_same]
  have hrankP : elementaryAbelianPRank p ↥P ≤ 1 := by
    by_contra hcon
    obtain ⟨A, hcomm, hexp, hcard⟩ := (mem_elementaryAbelianRanks_iff_exists_subgroup hp
      (X := ↥P) (d := 2)).1 ((le_elementaryAbelianPRank_iff hp.one_lt).1 (by omega))
    exact not_isCyclic_of_isElementaryAbelian_of_natCard_eq_pow hp
      (isElementaryAbelian_iff.2 ⟨hcomm, hexp⟩) hcard le_rfl hPcyc
  have hrankM : elementaryAbelianPRank p ↥M = 1 := by
    have h1 : elementaryAbelianPRank p ↥P = elementaryAbelianPRank p ↥M :=
      elementaryAbelianPRank_eq_of_le_of_factorization_eq hp hPM hfac
    have h2 : 1 ≤ elementaryAbelianPRank p ↥M := (one_le_elementaryAbelianPRank_iff hp).2 hpM
    omega
  have hpτ : p ∈ tau1Primes M ∪ tau3Primes M := by
    rw [tau1Primes_union_tau3Primes]
    exact ⟨hp, hpM, hpσ, hrankM⟩
  obtain ⟨y, hyX, hy⟩ := exists_mem_orderOf_eq_of_dvd hp hpX
  have hYcard : Nat.card ↥(zpowers y) = p := by rw [Nat.card_zpowers, hy]
  have hYX : (zpowers y : Subgroup G) ≤ X := zpowers_le.2 hyX
  have hYP : (zpowers y : Subgroup G) ≤ P := hYX.trans hXP
  have hYne : (zpowers y : Subgroup G) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hYcard
    exact hp.one_lt.ne hYcard
  have hYp : IsPGroup p (zpowers y) := IsPGroup.of_card (by rw [pow_one, hYcard])
  obtain ⟨L, hL, hNL⟩ := exists_isCoatom_ge_of_ne_top
    (normalizer_lt_top_of_isPGroup hG.not_isMulCommutative hp hYne hYp).ne
  have hPcomm : IsMulCommutative ↥P := @IsCyclic.isMulCommutative _ _ hPcyc
  have hPcentY : P ≤ centralizer ((zpowers y : Subgroup G) : Set G) :=
    (le_centralizer_iff_isMulCommutative.2 hPcomm).trans
      (centralizer_le (SetLike.coe_subset_coe.2 hYP))
  have hPL : P ≤ L := hPcentY.trans ((centralizer_le_normalizer _).trans hNL)
  obtain ⟨-, hcent, hsigma⟩ := h₂ G hGmin M hMcoatom E hEM hsd p hpτ (zpowers y)
    (hYP.trans hPM) hYcard L hL hNL
  have hkey : (sigmaCore M ⊓ L : Subgroup G) ≤ centralizer (P : Set G) := by
    by_cases hc : (⁅sigmaCore M ⊓ L, M ⊓ L⁆ : Subgroup G) = ⊥
    · exact (commutator_eq_bot_iff_le_centralizer.1 hc).trans
        (centralizer_le (SetLike.coe_subset_coe.2 (le_inf hPM hPL)))
    · have hpσL : p ∈ sigmaPrimes L := (hsigma hc).1
      have hτ₁L : ∀ s ∈ (Nat.card ↥P).primeFactors, s ∉ tau1Primes L := by
        intro s hs hsτ
        obtain ⟨hsp, hsd, -⟩ := Nat.mem_primeFactors.1 hs
        rw [hcardP] at hsd
        have hsp' : s = p := (Nat.prime_dvd_prime_iff_eq hsp hp).1 (hsp.dvd_of_dvd_pow hsd)
        exact notMem_sigmaPrimes_of_mem_tau1Primes (hsp' ▸ hsτ) hpσL
      exact le_centralizer_iff.1 (hcent P (le_inf hPE hPL) hτ₁L)
  refine le_antisymm ?_ (inf_le_inf_left _ (centralizer_le (SetLike.coe_subset_coe.2 hXP)))
  have hstep : (sigmaCore M ⊓ centralizer (X : Set G) : Subgroup G) ≤ sigmaCore M ⊓ L :=
    inf_le_inf_left _ ((centralizer_le (SetLike.coe_subset_coe.2 hYX)).trans
      ((centralizer_le_normalizer _).trans hNL))
  exact le_inf inf_le_left (hstep.trans hkey)

end

end CFSG.FeitThompson.Proofs
