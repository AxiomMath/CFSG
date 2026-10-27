module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.OutsideSigmaPlaneComplementNormalizer
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.SigmaComplementThreeHallFactors
import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.PrimeFixedMinimalQuotient
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters
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

open Subgroup CFSG.FeitThompson

universe u

theorem FTS_core_nonregular_element_with_tau_two_prime
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_tau12_fixed_plane_line_core_free.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_tau13_nonfree_third_factor_structure.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_core_nonregular_element_with_tau_two_prime.{u} := by
  intro G _ _ hG M hM E hEM hsd y hyE hy1 hCy hex p hpy
  obtain ⟨q, hqy, hq⟩ := hex
  by_contra hpτ₂
  have hG04 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hG05 : CFSG.FeitThompson.Prep05.IsMinimalSimpleOdd G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hsc : _root_.CFSG.FeitThompson.IsSigmaComplement M E := ⟨hM, hsd⟩
  obtain ⟨hπE, hrank, -, -, -, -, -, -⟩ := FNI_sigma_complement_prime_data h₁ G hG04 M E hsc
  obtain ⟨hp, hpd, -⟩ := Nat.mem_primeFactors.1 hpy
  have hyord : orderOf y ∣ Nat.card ↥E := E.orderOf_dvd_natCard hyE
  have hpE : p ∣ Nat.card ↥E := hpd.trans hyord
  have hpM : p ∣ Nat.card ↥M := hpE.trans (Subgroup.card_dvd_of_le hEM)
  have hpmem : p ∈ _root_.CFSG.FeitThompson.primeDivisorsOf ↥E := ⟨hp, hpE⟩
  have hpσ : p ∉ sigmaPrimes M := (hπE.le hpmem).2
  obtain ⟨-, hrpM2⟩ := hrank p hpmem
  have hrpM1 : 1 ≤ elementaryAbelianPRank p ↥M := (one_le_elementaryAbelianPRank_iff hp).2 hpM
  have hrM1 : elementaryAbelianPRank p ↥M = 1 := by
    rcases Nat.lt_or_ge (elementaryAbelianPRank p ↥M) 2 with h | h
    · omega
    · exact absurd (mem_tauTwoPrimes_iff.2 ⟨hp, hpσ, by omega⟩) hpτ₂
  have hpτ13 : p ∈ tau1Primes M ∪ tau3Primes M := by
    rw [tau1Primes_union_tau3Primes]
    exact ⟨hp, hpM, hpσ, hrM1⟩
  obtain ⟨x, hxy, hxord⟩ := exists_mem_orderOf_eq_of_dvd (H := zpowers y) hp
    (by rw [Nat.card_zpowers]; exact hpd)
  have hycomm : (zpowers y : Subgroup G) ≤ centralizer ((zpowers y : Subgroup G) : Set G) :=
    le_centralizer_iff_isMulCommutative.2 inferInstance
  have hyEsub : (zpowers y : Subgroup G) ≤ E := zpowers_le.2 hyE
  have hPy : (zpowers x : Subgroup G) ≤ zpowers y := zpowers_le.2 hxy
  have hPE : (zpowers x : Subgroup G) ≤ E := hPy.trans hyEsub
  have hPcard : Nat.card ↥(zpowers x : Subgroup G) = p := by rw [Nat.card_zpowers, hxord]
  have hcentle : centralizer ({y} : Set G) ≤ centralizer ((zpowers x : Subgroup G) : Set G) := by
    rw [← centralizer_coe_zpowers y]
    exact centralizer_le (SetLike.coe_subset_coe.2 hPy)
  have hCP : sigmaCore M ⊓ centralizer ((zpowers x : Subgroup G) : Set G) ≠ ⊥ := by
    intro h
    exact hCy (le_bot_iff.1 (h ▸ inf_le_inf_left (sigmaCore M) hcentle))
  rcases hpτ13 with hpτ₁ | hpτ₃
  ·
    obtain ⟨hqp, hqd, -⟩ := Nat.mem_primeFactors.1 hqy
    have hqE : q ∣ Nat.card ↥E := hqd.trans hyord
    obtain ⟨hrqE, -⟩ := hrank q ⟨hqp, hqE⟩
    have hrqE2 : elementaryAbelianPRank q ↥E = 2 :=
      hrqE.trans (elementaryAbelianPRank_eq_two_of_mem_tauTwoPrimes hq)
    obtain ⟨A₀, ⟨e⟩⟩ := mem_elementaryAbelianRanks.1
      (hrqE2 ▸ elementaryAbelianPRank_mem_elementaryAbelianRanks (X := ↥E) (p := q) hqp.one_lt)
    set A : Subgroup G := A₀.map E.subtype with hA
    have hAE : A ≤ E := map_subtype_le _
    have hAplane : _root_.CFSG.FeitThompson.IsElementaryAbelianPlane q A :=
      ⟨(A₀.equivMapOfInjective E.subtype E.subtype_injective).symm.trans e⟩
    have hAosp : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane q M A :=
      ⟨hM, hqp, notMem_sigmaPrimes_of_mem_tauTwoPrimes hq, hAE.trans hEM, hAplane⟩
    obtain ⟨-, hXA, -, -, -⟩ :=
      FNI_outside_sigma_plane_complement_normalizer h₂ h₅ h₆ G hG04 q M A E hAosp hsc hAE
    obtain ⟨z, hzy, hzord⟩ := exists_mem_orderOf_eq_of_dvd (H := zpowers y) hqp
      (by rw [Nat.card_zpowers]; exact hqd)
    have hQy : (zpowers z : Subgroup G) ≤ zpowers y := zpowers_le.2 hzy
    have hQcard : Nat.card ↥(zpowers z : Subgroup G) = q := by rw [Nat.card_zpowers, hzord]
    have hQA : (zpowers z : Subgroup G) ≤ A := hXA _ (hQy.trans hyEsub) hQcard
    have hQcent : (zpowers z : Subgroup G) ≤ centralizer ((zpowers x : Subgroup G) : Set G) :=
      (hQy.trans hycomm).trans (centralizer_le (SetLike.coe_subset_coe.2 hPy))
    have hQne : (zpowers z : Subgroup G) ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hQcard
      exact hqp.ne_one hQcard.symm
    have hAcent : A ⊓ centralizer ((zpowers x : Subgroup G) : Set G) ≠ ⊥ := fun h =>
      hQne (le_bot_iff.1 (h ▸ le_inf hQA hQcent))
    exact hCP (h₃ G hG04 p q M E (zpowers x) A hsc hpτ₁ hPE hPcard hq hAE hAplane hAcent)
  ·
    obtain ⟨E₁, E₂, E₃, hsplit, -⟩ := FNI_sigma_complement_three_factors h₁ G hG04 M E hsc
    have : (E₃.subgroupOf E).Normal := hsplit.outer.normal_subgroupOf
    have hPsubcard : Nat.card ↥((zpowers x : Subgroup G).subgroupOf E) = p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPE).toEquiv, hPcard]
    have hPpi : IsPiSubgroup (tau3Primes M) ((zpowers x : Subgroup G).subgroupOf E) := by
      refine isPiSubgroup_iff.2 fun r hr => ?_
      rw [hPsubcard, hp.primeFactors, Finset.mem_singleton] at hr
      exact hr ▸ hpτ₃
    have hPsub := hsplit.isHall_E₃.le_of_isPiSubgroup hPpi
    have hxE₃ : x ∈ E₃ := by
      have hx' : (⟨x, hPE (mem_zpowers x)⟩ : ↥E) ∈ (zpowers x : Subgroup G).subgroupOf E :=
        mem_subgroupOf.2 (mem_zpowers x)
      exact mem_subgroupOf.1 (hPsub hx')
    have hxne : x ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hxord
      exact hp.ne_one hxord.symm
    have htf :
        CFSG.FeitThompson.Prep05.IsTauFactorization M E E₁ E₂ E₃ :=
      ⟨⟨hM, hsd⟩, hsplit.le_E₁, hsplit.le_E₂, hsplit.le_E₃, hsplit.isHall_E₁, hsplit.isHall_E₂,
        hsplit.isHall_E₃, hsplit.outer, hsplit.inner, hsplit.isCyclic_E₁, hsplit.isCyclic_E₃,
        hsplit.le_commutator_E₃, hsplit.normal_E₂_sup_E₃, hsplit.centralizer_E₃⟩
    obtain ⟨hE₂, -⟩ := h₄ G hG05 M E E₁ E₂ E₃ htf ⟨x, hxE₃, hxne, hCP⟩
    obtain ⟨hqp, hqd, -⟩ := Nat.mem_primeFactors.1 hqy
    have hqE : q ∣ Nat.card ↥E := hqd.trans hyord
    have hidx : (E₂.subgroupOf E).index = Nat.card ↥E := by
      rw [hE₂, bot_subgroupOf, index_bot]
    exact hsplit.isHall_E₂.notMem_of_mem_primeFactors_index q
      (by rw [hidx]; exact Nat.mem_primeFactors.2 ⟨hqp, hqE, Nat.card_pos.ne'⟩) hq

end

end CFSG.FeitThompson.Proofs
