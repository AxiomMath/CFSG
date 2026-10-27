module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.TauOneIntersectionRegularSylow
import CFSG.FeitThompson.Local.TauOneLineRegularSylowCentralizerBound
import CFSG.FeitThompson.Local.BetaCoreHallQuotient
import CFSG.FeitThompson.Local.TwoBetaFixedCoresHallPosition
import CFSG.FeitThompson.Local.RegularTauOneSylowBetaFixedPoints
import CFSG.FeitThompson.Local.TypeIISupportingMaximumExcludesPair
import CFSG.FeitThompson.Local.NilpotentDerivedQuotientPrimeCommutator
import CFSG.FeitThompson.Local.MixedFittingCentralizerConstrained
import CFSG.FeitThompson.Local.NilpotentSigmaPrimeSeparation
import CFSG.FeitThompson.Local.AlphaSigmaPrimeSeparation
import CFSG.FeitThompson.Local.CriticalRegularComplementFixedPoints
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.NormalComplementDerivedIntersection
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
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

open CFSG.FeitThompson CFSG.FeitThompson
open Subgroup Pointwise

universe u

theorem ne_conjSubgroup_symm {G : Type*} [Group G] {M L : Subgroup G}
    (h : ∀ g : G, L ≠ conjSubgroup M g) : ∀ g : G, M ≠ conjSubgroup L g := by
  intro g hMg
  refine h g⁻¹ ?_
  rw [hMg]
  exact (conjSubgroup_conjSubgroup_inv L g).symm

theorem false_of_hall_position_of_regular_tau_one_sylow
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FTS_admissible_tau_one_prime_centralizer_inclusion.{u})
    (h₄ : Statements.FTS_proper_subgroup_p_length_one.{u})
    {G : Type u} [Group G] [Finite G] (hG : IsOddOrderMinimalSimple G)
    {M₀ L₀ P Q H : Subgroup G} {p q s r : ℕ}
    (hM₀ : IsCoatom M₀) (hL₀ : IsCoatom L₀) (hnc : ∀ g : G, L₀ ≠ conjSubgroup M₀ g)
    (hp : p.Prime) (hpM₀ : p ∈ tau1Primes M₀) (hpL₀ : p ∈ tau1Primes L₀)
    (hPML : P ≤ M₀ ⊓ L₀) (hPcard : Nat.card ↥P = p)
    (hq : q.Prime) (hqp : q ≠ p) (hQM : IsSylowSubgroupOf q Q M₀) (hQbot : Q ≠ ⊥)
    (hPQ : P ≤ normalizer (Q : Set G)) (hQfix : Q ⊓ centralizer (P : Set G) = ⊥)
    (hNQL : normalizer (Q : Set G) ≤ L₀) (hqβ : q ∉ betaPrimes ↥M₀)
    (hfix₂ : betaCore M₀ ⊓ centralizer ((P : Set G) * (Q : Set G)) = ⊥)
    (hHle : H ≤ (centralizer (P : Set G) ⊓ M₀ : Subgroup G))
    (hrβ : r ∈ betaPrimes ↥L₀) (hrH : r ∣ Nat.card ↥H)
    (hXne : CFSG.FeitThompson.pCoreIn s H ≠ ⊥) (hXB : CFSG.FeitThompson.pCoreIn s H ≤ betaCore M₀) :
    False := by
  let _i : Fintype G := Fintype.ofFinite G
  have _i2 := hG.isSimpleGroup
  have _iq := Fact.mk hq
  set X : Subgroup G := CFSG.FeitThompson.pCoreIn s H with hXdef
  have hXH : X ≤ H := CFSG.FeitThompson.pCoreIn_le s H
  have hXC : X ≤ centralizer (P : Set G) := (hXH.trans hHle).trans inf_le_left
  have hPM : P ≤ M₀ := hPML.trans inf_le_left
  have hPL : P ≤ L₀ := hPML.trans inf_le_right
  have hQL : Q ≤ L₀ := le_trans Subgroup.le_normalizer hNQL
  have hQM' : Q ≤ M₀ := hQM.1
  have hr : r.Prime := prime_of_mem_betaPrimes hrβ
  have hrC : r ∣ Nat.card ↥(M₀ ⊓ centralizer (P : Set G) : Subgroup G) :=
    hrH.trans (Subgroup.card_dvd_of_le (hHle.trans (le_of_eq (inf_comm _ _))))
  have htrans := FBG_tau_one_fixed_core_transfer h₁ h₂ h₄ G hG M₀ L₀ hM₀ hL₀ hnc p hp hpM₀ hpL₀
    P hPML hPcard q hq hqp Q hQM hQbot hPQ hQfix hNQL r hr hrβ hrC
  have hBS : betaCore M₀ ≤ sigmaCore M₀ :=
    le_sigmaCore (betaCore_le M₀) (betaCore_normal_subgroupOf M₀)
      ((isPiSubgroup_betaCore M₀).mono
        (betaPrimes_subset_sigmaPrimes hG.not_isMulCommutative hG.odd_natCard
          hG.isSolvable_of_ne_top hM₀))
  have hXL : X ≤ L₀ := fun x hx => htrans (Subgroup.mem_inf.2 ⟨hBS (hXB hx), hXC hx⟩)
  set V : Subgroup G := betaCore M₀ ⊓ L₀ with hVdef
  have hXV : X ≤ V := le_inf hXB hXL
  have hVL : V ≤ L₀ := inf_le_right
  have hQnB : Q ≤ normalizer ((betaCore M₀ : Subgroup G) : Set G) :=
    hQM'.trans (le_normalizer_betaCore M₀)
  have hQnV : Q ≤ normalizer ((V : Subgroup G) : Set G) :=
    le_trans (le_inf hQnB (hQL.trans Subgroup.le_normalizer))
      Subgroup.inf_normalizer_le_normalizer_inf
  have hQp : IsPGroup q ↥Q := IsPGroup.of_card hQM.2
  have hMsolv : Group.IsSolvable ↥M₀ := hG.isSolvable_of_ne_top M₀ hM₀.1
  have _i3 : Group.IsSolvable ↥P := isSolvable_of_le_of_isSolvable hPM hMsolv
  have _i4 : Group.IsSolvable ↥Q := isSolvable_of_le_of_isSolvable hQM' hMsolv
  have hcop : (Nat.card ↥P).Coprime (Nat.card ↥Q) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQp
    rw [hPcard, hn]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp hq).2 (Ne.symm hqp))
  have hQcomm : Q ≤ (⁅L₀, L₀⁆ : Subgroup G) :=
    (le_commutator_of_coprime_of_inf_centralizer_eq_bot hPQ hcop hQfix).trans
      (Subgroup.commutator_mono hQL hPL)
  have hG6 : _root_.CFSG.FeitThompson.Prep06.IsMinimalOddSimple G :=
    { odd := hG.odd_natCard, simple := hG.isSimpleGroup,
      nonabelian := hG.not_isMulCommutative, solvable := hG.isSolvable_of_ne_top }
  obtain ⟨-, -, hSL⟩ := h₁ G hG L₀ hL₀
  have hBL' : betaCore L₀ ≤ (⁅L₀, L₀⁆ : Subgroup G) := betaCore_le_commutator hG6 hL₀ hSL
  have _i5 : ((betaCore L₀).subgroupOf (⁅L₀, L₀⁆ : Subgroup G)).Normal :=
    normal_subgroupOf_betaCore_commutator hG6 hL₀ hSL
  have hnil0 : Group.IsNilpotent
      (↥(⁅L₀, L₀⁆ : Subgroup G) ⧸ (betaCore L₀).subgroupOf (⁅L₀, L₀⁆ : Subgroup G)) :=
    Group.nilpotent_of_mulEquiv (_h := isNilpotent_quotient_piCore_commutator h₄ hG6 hL₀)
      (QuotientGroup.quotientMulEquivOfEq (subgroupOf_betaCore_commutator hG6 hL₀ hSL).symm)
  have _i6 : ((betaCore L₀).subgroupOf L₀).Normal := betaCore_normal_subgroupOf L₀
  have _i7 : ((⁅L₀, L₀⁆ : Subgroup G).subgroupOf L₀).Normal :=
    CFSG.FeitThompson.normal_subgroupOf_commutator_self L₀
  have _i8 : (((betaCore L₀).subgroupOf L₀).subgroupOf
      ((⁅L₀, L₀⁆ : Subgroup G).subgroupOf L₀)).Normal := Subgroup.Normal.subgroupOf _i6 _
  have hnil : Group.IsNilpotent (↥((⁅L₀, L₀⁆ : Subgroup G).subgroupOf L₀) ⧸
      ((betaCore L₀).subgroupOf L₀).subgroupOf ((⁅L₀, L₀⁆ : Subgroup G).subgroupOf L₀)) :=
    Group.nilpotent_of_mulEquiv (_h := hnil0)
      (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_self L₀))
        (map_subgroupOf_subgroupOfEquivOfLe (Subgroup.commutator_le_self L₀))).symm
  have hcommeq : _root_.commutator ↥L₀ = (⁅L₀, L₀⁆ : Subgroup G).subgroupOf L₀ :=
    commutator_eq_subgroupOf_commutator L₀
  have hDle : (betaCore L₀).subgroupOf L₀ ≤ _root_.commutator ↥L₀ := by
    rw [hcommeq]; exact Subgroup.comap_mono hBL'
  have hnilC : Group.IsNilpotent (↥(_root_.commutator ↥L₀) ⧸
      ((betaCore L₀).subgroupOf L₀).subgroupOf (_root_.commutator ↥L₀)) := by
    rw [hcommeq]; exact hnil
  have hVπ : IsPiSubgroup (betaPrimes ↥M₀) V := (isPiSubgroup_betaCore M₀).of_le inf_le_left
  have hVq : ¬ q ∣ Nat.card ↥V := fun hdvd =>
    hqβ (isPiSubgroup_iff.1 hVπ q (Nat.mem_primeFactors.2 ⟨hq, hdvd, Nat.card_pos.ne'⟩))
  have hVcop : (Nat.card ↥V).Coprime q := ((Nat.Prime.coprime_iff_not_dvd hq).2 hVq).symm
  have hcomm207 := commutator_le_of_isNilpotent_commutator_quotient (L := ↥L₀)
      (q := q) (D := (betaCore L₀).subgroupOf L₀) hDle hnilC
      (Q := Q.subgroupOf L₀) (V := V.subgroupOf L₀)
      (by rw [hcommeq]; exact Subgroup.comap_mono hQcomm)
      hQp.comap_subtype
      (by rw [natCard_subgroupOf_of_le hVL]; exact hVcop)
      (le_normalizer_subgroupOf hQnV)
  have hVQ : ⁅V, Q⁆ ≤ betaCore L₀ := by
    rw [commutator_subgroupOf hVL hQL] at hcomm207
    exact le_of_subgroupOf_le_subgroupOf
      ((Subgroup.commutator_mono hVL hQL).trans (Subgroup.commutator_le_self L₀)) hcomm207
  have hXQ_L : ⁅X, Q⁆ ≤ betaCore L₀ := (Subgroup.commutator_mono hXV le_rfl).trans hVQ
  have hXQ_M : ⁅X, Q⁆ ≤ betaCore M₀ :=
    (Subgroup.commutator_mono hXB le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.1 hQnB)
  have hconj : ∀ g : G, MulAut.conj g • M₀ ≠ L₀ := by
    intro g hgl
    refine hnc g⁻¹ ?_
    rw [← hgl]
    simp [CFSG.FeitThompson.conjSubgroup, conj_smul_eq_map_conj]
  have hdisjβ : betaPrimes ↥M₀ ∩ betaPrimes ↥L₀ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro t ⟨htM, htL⟩
    exact Set.disjoint_left.mp
      (disjoint_sigmaPrimes_alphaPrimes_of_not_conj hG.not_isMulCommutative hG.odd_natCard
        hG.isSolvable_of_ne_top hM₀ hL₀ hconj)
      (betaPrimes_subset_sigmaPrimes hG.not_isMulCommutative hG.odd_natCard
        hG.isSolvable_of_ne_top hM₀ htM)
      (betaPrimes_subset_alphaPrimes htL)
  have hBB : betaCore M₀ ⊓ betaCore L₀ = ⊥ :=
    inf_eq_bot_of_isPiSubgroup (isPiSubgroup_betaCore M₀) (isPiSubgroup_betaCore L₀) hdisjβ
  have hXQbot : ⁅X, Q⁆ = ⊥ :=
    le_bot_iff.1 (by rw [← hBB]; exact le_inf hXQ_M hXQ_L)
  have hXcQ : X ≤ centralizer (Q : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hXQbot
  have hfin : X ≤ betaCore M₀ ⊓ centralizer ((P : Set G) * (Q : Set G)) := by
    refine le_inf hXB ?_
    rw [centralizer_coe_mul_coe]
    exact le_inf hXC hXcQ
  rw [hfix₂, le_bot_iff] at hfin
  exact hXne hfin

theorem FBG_tau_one_intersection_asymmetry
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FTS_admissible_tau_one_prime_centralizer_inclusion.{u})
    (h₃ : Statements.FTS_beta_prime_centralizing_sylow.{u})
    (h₄ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FBG_tau_one_intersection_asymmetry.{u} := by
  intro G _ _ hG M L hM hL hnc p hp hpM hpL P hPML hPcard q u hq hu Q U hQ hU hPn hQfix hUfix
    hNQL hNUM
  have _i : Finite G := Finite.of_fintype G
  have hnc' : ∀ g : G, M ≠ conjSubgroup L g := ne_conjSubgroup_symm hnc
  have hPMLsymm : P ≤ L ⊓ M := le_inf (hPML.trans inf_le_right) (hPML.trans inf_le_left)
  have hU' : IsSylowSubgroupOf u U (L ⊓ M) := by
    rw [CFSG.FeitThompson.isSylowSubgroupOf_iff] at hU ⊢
    refine ⟨hU.1.trans (le_of_eq (inf_comm M L)), ?_⟩
    rw [hU.2, inf_comm M L]
  have hPQ : P ≤ normalizer (Q : Set G) := hPn.trans inf_le_left
  have hPU : P ≤ normalizer (U : Set G) := hPn.trans inf_le_right
  obtain ⟨hQbot, hQM, hqp, hqβ, -, hCBM, hfix₂M⟩ :=
    FBG_tau_one_intersection_regular_sylow h₃ G hG M L hM hL hnc p hp hpM P hPML hPcard q hq Q hQ
      hPQ hQfix hNQL
  obtain ⟨hUbot, hUL, hup, huβ, -, hCBL, hfix₂L⟩ :=
    FBG_tau_one_intersection_regular_sylow h₃ G hG L M hL hM hnc' p hp hpL P hPMLsymm hPcard u hu U
      hU' hPU hUfix hNUM
  have hPne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hPcard
    exact hp.one_lt.ne hPcard
  obtain ⟨M₀, L₀, horient, H, hHle, s, r, -, hrβ, -, -, hrH, hXne, -, hXB⟩ :=
    FBG_two_beta_fixed_cores_hall_position h₁ h₄ G hG M L hM hL hnc P hPML hPne hCBM hCBL
  rcases horient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact false_of_hall_position_of_regular_tau_one_sylow h₁ h₂ h₄ hG hM hL hnc hp hpM hpL hPML
      hPcard hq hqp hQM hQbot hPQ hQfix hNQL hqβ hfix₂M hHle hrβ hrH hXne hXB
  · exact false_of_hall_position_of_regular_tau_one_sylow h₁ h₂ h₄ hG hL hM hnc' hp hpL hpM
      hPMLsymm hPcard hu hup hUL hUbot hPU hUfix hNUM huβ hfix₂L hHle hrβ hrH hXne hXB

end

end CFSG.FeitThompson.Proofs
