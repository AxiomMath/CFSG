module

public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.NarrowSupportedPlaneCentralizesQSubgroup
import CFSG.FeitThompson.Local.ExceptionalPlaneMaximalElementaryAbelian
import CFSG.FeitThompson.Local.OutsideSigmaPlaneGloballyMaximal
import CFSG.FeitThompson.Local.CoprimeActionCyclicNoFixedPoint
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane
import CFSG.FeitThompson.Local.MaximalPlaneDerivedNormalComplement
import CFSG.FeitThompson.Local.ElementaryMaximalPLengthOneConstraint
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
import CFSG.FeitThompson.Local.PrimeCentralizerMinimalFittingAbelian
import CFSG.FeitThompson.Definitions.MaximalANormalizedQSubgroups
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
open Subgroup

universe u

variable {G : Type*} [Group G] [Finite G] {p q : ℕ}

theorem maximal_isElementaryAbelianSubgroup_of_maximal_isElementaryAbelian {X : Type*} [Group X]
    {A : Subgroup X} (h : Maximal (IsElementaryAbelian q) A) :
    Maximal (IsElementaryAbelianSubgroup q) A :=
  ⟨isElementaryAbelian_iff_isElementaryAbelianSubgroup.1 h.prop, fun _B hB hle =>
    h.le_of_ge (isElementaryAbelian_iff_isElementaryAbelianSubgroup.2 hB) hle⟩

theorem prime_dvd_natCard_of_isPGroup_of_ne_bot {H : Subgroup G} (hq : q.Prime)
    (hH : IsPGroup q H) (hne : H ≠ ⊥) : q ∣ Nat.card ↥H := by
  have := Fact.mk hq
  obtain ⟨n, hn⟩ := hH.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.card_eq_one.1 (by simpa using hn))
  rw [hn]
  exact dvd_pow_self q hn0

theorem commutator_eq_bot_of_isCyclic_of_inf_centralizer_ne_bot (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {A Q : Subgroup G} (hA : IsPGroup p A) (hQ : IsPGroup q Q) (hcyc : IsCyclic ↥Q)
    (hAQ : A ≤ normalizer (Q : Set G)) (hne : Q ⊓ centralizer (A : Set G) ≠ ⊥) :
    ⁅Q, A⁆ = ⊥ := by
  have := Fact.mk hp
  have := Fact.mk hq
  set φ : ↥A →* MulAut ↥Q := Q.normalizerMonoidHom.comp (Subgroup.inclusion hAQ) with hφ
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hxQ : x ∈ Q := hx.1
  have hxC : x ∈ centralizer (A : Set G) := hx.2
  have hfix : ∃ y : ↥Q, y ≠ 1 ∧ ∀ a : ↥A, φ a y = y := by
    refine ⟨⟨x, hxQ⟩, by simpa using hx1, fun a => ?_⟩
    apply Subtype.ext
    rw [hφ]
    have h := Subgroup.normalizerMonoidHom_apply_apply_coe Q (Subgroup.inclusion hAQ a) ⟨x, hxQ⟩
    simp only [MonoidHom.comp_apply]
    rw [h]
    have hcomm := (Subgroup.mem_centralizer_iff.1 hxC) (a : G) a.2
    simp only [Subgroup.coe_inclusion]
    rw [hcomm]
    group
  have hφ1 := eq_one_of_exists_ne_one_fixed hpq hA hQ φ hfix
  refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun y hy => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have h := congrArg (fun f => ((f (⟨a, ha⟩ : ↥A)) (⟨y, hy⟩ : ↥Q) : ↥Q)) hφ1
  simp only [MonoidHom.one_apply] at h
  have h2 : (a : G) * y * (a : G)⁻¹ = y := by
    have := congrArg (fun z : ↥Q => (z : G)) h
    simpa [hφ, Subgroup.normalizerMonoidHom_apply_apply_coe] using this
  exact mul_inv_eq_iff_eq_mul.mp h2

theorem exists_le_isElementaryAbelian_natCard_eq_sq_of_not_isCyclic (hq : q.Prime) (hqodd : Odd q)
    {Q : Subgroup G} (hQ : IsPGroup q Q) (hnc : ¬ IsCyclic ↥Q) :
    ∃ B : Subgroup G, B ≤ Q ∧ IsElementaryAbelian q B ∧ Nat.card ↥B = q ^ 2 := by
  have hnc' : ¬ IsCyclic ↥(⊤ : Subgroup ↥Q) := fun h =>
    hnc (isCyclic_of_surjective (⊤ : Subgroup ↥Q).subtype fun x => ⟨⟨x, trivial⟩, rfl⟩)
  obtain ⟨E, -, -, ⟨f⟩⟩ :=
    exists_normal_le_mulEquiv_pi_of_not_isCyclic hq hqodd hQ (⊤ : Subgroup ↥Q) hnc'
  refine ⟨E.map Q.subtype, Subgroup.map_subtype_le _,
    (isElementaryAbelian_of_nonempty_mulEquiv_pi ⟨f⟩).map_subtype, ?_⟩
  rw [Nat.card_congr (E.equivMapOfInjective Q.subtype Q.subtype_injective).symm.toEquiv,
    Nat.card_congr f.toEquiv, card_pi_multiplicative_zmod]

theorem FTS_exceptional_noncentral_sylow_fixed_free
    (h₁ : Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₂ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_exceptional_noncentral_sylow_fixed_free.{u} := by
  intro G _ _ hG p M A₀ A P hc q hq hqp hqσ Q hQM hAQ hQA
  by_contra hCne
  have : IsSimpleGroup G := hG.isSimpleGroup
  have hodd := hG.odd_natCard
  have hp : p.Prime := hc.prime
  have hAcard : Nat.card ↥A = p ^ 2 := hc.isElementaryAbelianPlane.natCard hp.ne_zero
  have hAea : IsElementaryAbelian p A := by
    obtain ⟨e⟩ := hc.isElementaryAbelianPlane
    exact isElementaryAbelian_of_nonempty_mulEquiv_pi ⟨e⟩
  have hApg : IsPGroup p A := IsPGroup.of_card hAcard
  have hQpg : IsPGroup q Q := IsPGroup.of_card hQM.2
  have hQne : Q ≠ ⊥ := fun h => hCne (by rw [h]; exact bot_inf_eq _)
  have hqodd : Odd q :=
    Odd.of_dvd_nat hodd
      ((prime_dvd_natCard_of_isPGroup_of_ne_bot hq hQpg hQne).trans
        (Subgroup.card_subgroup_dvd_card Q))
  have hQnc : ¬ IsCyclic ↥Q := fun hcyc =>
    hQA (commutator_eq_bot_of_isCyclic_of_inf_centralizer_ne_bot hp hq (Ne.symm hqp) hApg hQpg
      hcyc hAQ hCne)
  obtain ⟨B, hBQ, hBea, hBcard⟩ :=
    exists_le_isElementaryAbelian_natCard_eq_sq_of_not_isCyclic hq hqodd hQpg hQnc
  have hBmax : Maximal (IsElementaryAbelian q) B :=
    maximal_isElementaryAbelian_of_plane_of_notMem_sigmaPrimes hq hG.not_isMulCommutative hodd
      hG.isSolvable hc.isCoatom (hBQ.trans hQM.1) hqσ hBea hBcard
  obtain ⟨-, -, -, hAmax0⟩ :=
    exceptional_maximal_plane (M := M) (A₀ := A₀) (A := A) (P := P) hG.not_isMulCommutative hodd
      hG.isSolvable hc.isCoatom hp hc.notMem_sigmaPrimes hc.natCard_A₀ hc.le_of_A₀ hc.le_of_A
      hc.le_of_P hc.isSylowSubgroupOf.2 hAea hAcard hc.normalizer_le
  have hAmax : Maximal (IsElementaryAbelian p) A :=
    ⟨hAea, fun E hE hAE => by
      by_contra hEA
      exact hAmax0 E hE (lt_of_le_not_ge hAE hEA)⟩
  obtain ⟨Qstar, hQstar, hQQstar⟩ := exists_mem_maximalNormalizedPSubgroups_ge hQpg hAQ
  have hBsub : Maximal (IsElementaryAbelianSubgroup q) (B.subgroupOf Qstar) :=
    maximal_isElementaryAbelianSubgroup_subgroupOf
      (maximal_isElementaryAbelianSubgroup_of_maximal_isElementaryAbelian hBmax)
      (hBQ.trans hQQstar)
  have hBsubcard : Nat.card ↥(B.subgroupOf Qstar) = q ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hBQ.trans hQQstar)).toEquiv, hBcard]
  have hqC : q ∣ Nat.card ↥(centralizer (A : Set G)) :=
    (prime_dvd_natCard_of_isPGroup_of_ne_bot hq (hQpg.to_le inf_le_left) hCne).trans
      (Subgroup.card_dvd_of_le inf_le_right)
  have hGmin : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hodd, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  obtain ⟨P', hAP', -, -, hcomm⟩ :=
    FTS_supported_plane_narrow_centralization h₁ h₂ G hGmin p q hp hq (Ne.symm hqp) A
      ⟨maximal_isElementaryAbelianSubgroup_of_maximal_isElementaryAbelian hAmax, hAcard⟩
      Qstar (isPGroup_of_mem hQstar) (le_normalizer_of_mem hQstar) hQstar hqC
      (Or.inr ⟨B.subgroupOf Qstar, hBsub, hBsubcard⟩)
  exact hQA (le_bot_iff.1 ((Subgroup.commutator_mono hQQstar hAP').trans
    (le_of_eq (by rw [Subgroup.commutator_comm]; exact hcomm))))

end

end CFSG.FeitThompson.Proofs
