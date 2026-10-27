module

public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.InvariantComplementFittingSelfCentralizing
import CFSG.FeitThompson.Local.NilpotentDerivedQuotientPrimeCommutator
import CFSG.FeitThompson.Local.MixedFittingCentralizerConstrained
import CFSG.FeitThompson.Local.PComplCoreCentralizerInAmbient
import CFSG.FeitThompson.Representations.DadeSignalizersCanonicalNormalHall
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import CFSG.FeitThompson.Local.CoprimeSolvableCommutatorDecomposition

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

variable {G : Type*} [Group G]

theorem commutator_eq_of_inf_centralizer_eq_bot [Finite G] {U K : Subgroup G}
    (hUab : IsMulCommutative ↥U) (hKU : K ≤ normalizer (U : Set G))
    (hcop : (Nat.card ↥K).Coprime (Nat.card ↥U))
    (hC : U ⊓ centralizer (K : Set G) = ⊥) : ⁅U, K⁆ = U := by
  set W : Subgroup G := U ⊔ K with hW
  have hUW : U ≤ W := le_sup_left
  have hKW : K ≤ W := le_sup_right
  have hUn : ((U.subgroupOf W)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hUW).2 (sup_le le_normalizer hKU)
  have hUab' : IsMulCommutative ↥(U.subgroupOf W) := subgroupOf_isMulCommutative W U
  have hcop' : (Nat.card ↥(K.subgroupOf W)).Coprime (Nat.card ↥(U.subgroupOf W)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hKW).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hUW).toEquiv]
    exact hcop
  have h := sup_inf_centralizer_commutator_eq (U.subgroupOf W) (K.subgroupOf W) hUab' hcop'
  have h2 := congrArg (fun S : Subgroup ↥W => S.map W.subtype) h
  simp only [Subgroup.map_sup, Subgroup.map_commutator, map_subgroupOf_eq_of_le hUW,
    map_subgroupOf_eq_of_le hKW] at h2
  have hfix : ((U.subgroupOf W) ⊓ centralizer ((K.subgroupOf W : Subgroup ↥W) : Set ↥W)).map
      W.subtype ≤ ⊥ := by
    rw [← hC]
    rintro x ⟨y, ⟨hyU, hyC⟩, rfl⟩
    refine ⟨hyU, mem_centralizer_iff.2 fun k hk => ?_⟩
    have := mem_centralizer_iff.1 hyC ⟨k, hKW hk⟩ (by simpa [mem_subgroupOf] using hk)
    exact congrArg Subtype.val this
  rw [le_bot_iff] at hfix
  rw [hfix, bot_sup_eq] at h2
  exact h2

theorem FTS_kappa_residual_contained_opposite_sigma_core
    (h₁ : Statements.FTS_kappa_residual_containing_complement_fitting.{u})
    (h₂ : Statements.FTS_kappa_residual_prime_overgroup_position.{u}) :
    Statements.FTS_kappa_residual_contained_opposite_sigma_core.{u} := by
  intro G _ _ hG r M K U A Mstar R H hP
  have hG' : Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable⟩
  have hsetup : Prep08.IsKappaResidualSetup M K U A Mstar R H r :=
    { isCoatom_M := hP.config.isCoatom
      kappa_nonempty := hP.config.kappaPrimes_nonempty
      isHall_K := ⟨hP.config.isHallKappa.1, hP.config.isHallKappa.2⟩
      isHall_U := ⟨hP.config.isHallCompl.1, hP.config.isHallCompl.2⟩
      semidirect_M := hP.config.isInternalSemidirectProduct
      semidirect_UK := hP.config.isInternalSemidirectProduct_complement
      isMulCommutative_U := hP.isMulCommutative_U
      centralizer_U := hP.centralizer_eq_bot
      U_ne_bot := hP.U_ne_bot
      A_eq := hP.A_eq
      isCoatom_Mstar := hP.isCoatom_Mstar
      exists_prime_order_le_K := hP.exists_prime_order_normalizer_le
      prime_r := hP.prime_r
      r_dvd := hP.dvd_natCard_U
      isSylow_R := (Prep08.isSylowOf_iff_natCard hP.prime_r hP.isSylowSubgroupOf_R.le).2
        hP.isSylowSubgroupOf_R.2
      isCoatom_H := hP.isCoatom_H
      normalizer_R_le := hP.normalizer_R_le }
  obtain ⟨hKprime, hUKH, -, -, -, -⟩ := h₂ G hG' M K U A Mstar R H r hsetup
  obtain ⟨⟨D, hDH, hsemi, hKD⟩, hall⟩ := h₁ G hG r M K U A Mstar R H hP
  obtain ⟨hKF, -⟩ := hall D hDH hsemi hKD
  set q : ℕ := Nat.card ↥K with hqdef
  have : Fact q.Prime := ⟨hKprime⟩
  have hFn : (fittingRaw ↥D).Normal := fittingRaw_normal ↥D
  have hFnil : Group.IsNilpotent ↥(fittingRaw ↥D) := isNilpotent_of_le_fittingRaw le_rfl
  obtain ⟨T, hTC, hTn, hTp, hTmax⟩ :=
    exists_normal_isPGroup_forall_le (q := q) (fittingRaw ↥D)
  set T' : Subgroup G := T.map D.subtype with hT'def
  have hT'D : T' ≤ D := map_subtype_le _
  have hKT' : K ≤ T' := by
    have h1 : K.subgroupOf D ≤ fittingRaw ↥D := by
      rw [← subgroupOf_fittingOfNormal D]
      exact comap_mono hKF
    have h2 : IsPGroup q ↥(K.subgroupOf D) :=
      IsPGroup.of_card (n := 1) (by
        rw [Nat.card_congr (subgroupOfEquivOfLe hKD).toEquiv, pow_one])
    have h3 := hTmax _ h1 h2
    have h4 := Subgroup.map_mono (f := D.subtype) h3
    rwa [map_subgroupOf_eq_of_le hKD] at h4
  have hT'norm : D ≤ normalizer (T' : Set G) := by
    refine (normal_subgroupOf_iff_le_normalizer hT'D).1 ?_
    rwa [hT'def, Subgroup.subgroupOf, comap_map_eq_self_of_injective D.subtype_injective]
  have hT'p : IsPGroup q ↥T' := hTp.map D.subtype
  set J : Subgroup G := sigmaCore H ⊔ T' with hJdef
  have hSH : sigmaCore H ≤ H := sigmaCore_le H
  have hHnS : H ≤ normalizer ((sigmaCore H : Subgroup G) : Set G) := le_normalizer_sigmaCore H
  have hJH : J ≤ H := sup_le hSH (hT'D.trans hDH)
  have hSJ : sigmaCore H ≤ J := le_sup_left
  have hHJ : H ≤ normalizer (J : Set G) := by
    intro h hh
    obtain ⟨s, hs, d, hd, rfl⟩ := hsemi.exists_mul hh
    exact mul_mem (Subgroup.le_normalizer (show s ∈ J from hSJ hs))
      (mem_normalizer_sup (hHnS (hDH hd)) (hT'norm hd))
  have hUH : U ≤ H := le_sup_left.trans hUKH
  have hKU : K ≤ normalizer (U : Set G) :=
    hP.config.isInternalSemidirectProduct_complement.right_le_normalizer
  have hKpi := isPiSubgroup_iff.1 hP.config.isHallKappa.isPiSubgroup
  have hUpi := isPiSubgroup_iff.1 hP.config.isHallCompl.isPiSubgroup
  have hcop : (Nat.card ↥K).Coprime (Nat.card ↥U) := by
    rw [← Nat.disjoint_primeFactors Nat.card_pos.ne' Nat.card_pos.ne', Finset.disjoint_left]
    intro p hpK hpU
    exact (hUpi p hpU).2.2 (hKpi p hpK)
  have hKne : K ≠ ⊥ := by
    intro h
    rw [hqdef, h, Subgroup.card_bot] at hKprime
    exact Nat.not_prime_one hKprime
  obtain ⟨k, hk, hk1⟩ : ∃ x ∈ K, x ≠ 1 := by
    rw [ne_eq, eq_bot_iff_forall] at hKne
    push Not at hKne
    exact hKne
  have hCUK : U ⊓ centralizer (K : Set G) = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [← hP.centralizer_eq_bot k hk hk1]
    exact inf_le_inf_left _ (centralizer_le (by simpa using hk))
  have hUcomm : ⁅U, K⁆ = U :=
    commutator_eq_of_inf_centralizer_eq_bot hP.isMulCommutative_U hKU hcop hCUK
  have hUJ : U ≤ J := by
    rw [← hUcomm]
    exact commutator_le_of_le_of_le_normalizer hUH hHJ (hKT'.trans le_sup_right)
  have hdisj : sigmaCore H ⊓ T' = ⊥ :=
    le_bot_iff.1 ((inf_le_inf_left _ hT'D).trans hsemi.inf_eq_bot.le)
  have hT'nS : T' ≤ normalizer ((sigmaCore H : Subgroup G) : Set G) :=
    (hT'D.trans hDH).trans hHnS
  have hSJn : ((sigmaCore H).subgroupOf J).Normal :=
    (normal_subgroupOf_iff_le_normalizer hSJ).2 (hJH.trans hHnS)
  have hidx : ((sigmaCore H).subgroupOf J).index = Nat.card ↥T' := by
    have h1 := Subgroup.index_mul_card ((sigmaCore H).subgroupOf J)
    rw [Nat.card_congr (subgroupOfEquivOfLe hSJ).toEquiv,
      natCard_sup_eq_mul_of_le_normalizer hT'nS hdisj] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans (mul_comm _ _))
  have hcopUT : (Nat.card ↥U).Coprime (Nat.card ↥T') := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hT'p
    rw [hn]
    exact Nat.Coprime.pow_right n hcop.symm
  have hfin : U.subgroupOf J ≤ (sigmaCore H).subgroupOf J := by
    refine le_of_coprime_natCard_index ?_
    rw [Nat.card_congr (subgroupOfEquivOfLe hUJ).toEquiv, hidx]
    exact hcopUT
  have hlast := Subgroup.map_mono (f := J.subtype) hfin
  rwa [map_subgroupOf_eq_of_le hUJ, map_subgroupOf_eq_of_le hSJ] at hlast

end

end CFSG.FeitThompson.Proofs
