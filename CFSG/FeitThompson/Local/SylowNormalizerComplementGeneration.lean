module

public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.SylowNormalizerDerivedSubgroup
import CFSG.FeitThompson.Foundations.SolvableHallExistence
import CFSG.FeitThompson.Local.CommonPrimeFixedComplementLayout
import CFSG.FeitThompson.Local.NormalComplementDerivedIntersection
import CFSG.FeitThompson.Local.SolvableDerivedKernelCommutators
import CFSG.FeitThompson.Local.NormalComplementSylowDerivedIntersection
import CFSG.FeitThompson.Local.NilpotentDerivedNormalizerFactorization
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
public import Mathlib
import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson

universe u

private theorem natCard_subgroupOf_eq_of_le' {G : Type*} [Group G] {M P : Subgroup G}
    (h : P ≤ M) : Nat.card (P.subgroupOf M) = Nat.card P := by
  have e := Subgroup.equivMapOfInjective (P.subgroupOf M) M.subtype M.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le h] at e
  exact Nat.card_congr e.toEquiv

theorem FPL_global_sylow_complement_generation
    (h₁ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FPL_global_sylow_complement_generation.{u} := by
  intro G _ _ hG p hp P hPne hPsyl L hL
  subst hL
  have := Fact.mk hp
  have := hG.simple
  have : Finite G := Finite.of_fintype G
  obtain ⟨-, hPcard⟩ := hPsyl
  rw [Subgroup.card_top] at hPcard
  have hPp : IsPGroup p P := IsPGroup.of_card hPcard
  have hLne : (normalizer (P : Set G)) ≠ ⊤ :=
    (normalizer_lt_top_of_isPGroup hG.nonabelian hp hPne hPp).ne
  have hLsol : Group.IsSolvable ↥(normalizer (P : Set G)) := hG.solvable _ hLne
  have hPL : P ≤ normalizer (P : Set G) := Subgroup.le_normalizer
  have hPLn : (P.subgroupOf (normalizer (P : Set G))).Normal := Subgroup.normal_in_normalizer
  have hPLcard : Nat.card (P.subgroupOf (normalizer (P : Set G)))
      = p ^ (Nat.card ↥(normalizer (P : Set G))).factorization p := by
    rw [natCard_subgroupOf_eq_of_le' hPL]
    exact natCard_eq_pow_factorization_of_le hp hPL hPcard
  set SP : Sylow p ↥(normalizer (P : Set G)) := Sylow.ofCard _ hPLcard with hSP
  have hSPcoe : (SP : Subgroup ↥(normalizer (P : Set G))) = P.subgroupOf (normalizer (P : Set G)) :=
    Sylow.coe_ofCard _ _
  have hmapP : Subgroup.map (normalizer (P : Set G)).subtype
      (P.subgroupOf (normalizer (P : Set G))) = P := Subgroup.map_subgroupOf_eq_of_le hPL
  constructor
  ·
    obtain ⟨H, hH⟩ := exists_isHallSubgroup (X := ↥(normalizer (P : Set G))) ({p}ᶜ)
    refine ⟨H.map (normalizer (P : Set G)).subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
    · have hcard : Nat.card (H.map (normalizer (P : Set G)).subtype) = Nat.card H :=
        (Nat.card_congr (Subgroup.equivMapOfInjective H _
          (normalizer (P : Set G)).subtype_injective).toEquiv).symm
      rw [hcard]
      intro hdvd
      exact isPiNumber_iff.1 hH.natCard p
        (Nat.mem_primeFactors.2 ⟨hp, hdvd, Nat.card_pos.ne'⟩) rfl
    · have hsub : (H.map (normalizer (P : Set G)).subtype).subgroupOf
          (normalizer (P : Set G)) = H :=
        Subgroup.comap_map_eq_self_of_injective (normalizer (P : Set G)).subtype_injective H
      have heq : (H.map (normalizer (P : Set G)).subtype).relIndex (normalizer (P : Set G))
          = H.index := by rw [Subgroup.relIndex, hsub]
      rw [heq]
      refine exists_eq_pow_of_isPiNumber_singleton Subgroup.index_ne_zero_of_finite ?_
      simpa using hH.index
  · intro V hVL hVp ⟨k, hVk⟩
    have hVsub : Nat.card (V.subgroupOf (normalizer (P : Set G))) = Nat.card V :=
      natCard_subgroupOf_eq_of_le' hVL
    have hidx : (V.subgroupOf (normalizer (P : Set G))).index = p ^ k := by
      rw [← hVk]; rfl
    have hcompl := isComplement'_sylow_of_index_eq_pow hp (by rw [hVsub]; exact hVp) hidx SP
    rw [hSPcoe] at hcompl
    have hsup : V ⊔ P = normalizer (P : Set G) := by
      have h := congrArg (Subgroup.map (normalizer (P : Set G)).subtype) hcompl.sup_eq_top
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hVL, hmapP,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
      exact h
    have hinf : P ⊓ V = ⊥ := by
      have h := congrArg (Subgroup.map (normalizer (P : Set G)).subtype)
        (disjoint_iff.1 hcompl.disjoint)
      rw [Subgroup.map_inf _ _ _ (normalizer (P : Set G)).subtype_injective,
        Subgroup.map_subgroupOf_eq_of_le hVL, hmapP, Subgroup.map_bot] at h
      rw [inf_comm]; exact h
    refine ⟨by rw [sup_comm]; exact hsup, hinf, ?_, ?_, ?_⟩
    ·
      have hder : P ≤ ⁅normalizer (P : Set G), normalizer (P : Set G)⁆ :=
        FPL_global_sylow_normalizer_derived h₁ G hG p hp P hPne ⟨le_top, by
          rw [Subgroup.card_top]; exact hPcard⟩
      have hderL : P.subgroupOf (normalizer (P : Set G))
          ≤ _root_.commutator ↥(normalizer (P : Set G)) := by
        rw [commutator_eq_subgroupOf_commutator]
        exact Subgroup.subgroupOf_mono _ hder
      have hsup' : P.subgroupOf (normalizer (P : Set G))
          ⊔ V.subgroupOf (normalizer (P : Set G)) = ⊤ := by
        rw [sup_comm]; exact hcompl.sup_eq_top
      have hinf' : P.subgroupOf (normalizer (P : Set G))
          ⊓ V.subgroupOf (normalizer (P : Set G)) = ⊥ := by
        rw [inf_comm]; exact disjoint_iff.1 hcompl.disjoint
      have hcc := eq_commutator_of_isSolvable_of_le_commutator
        (P.subgroupOf (normalizer (P : Set G))) (V.subgroupOf (normalizer (P : Set G)))
        hsup' hinf' hderL
      have h := congrArg (Subgroup.map (normalizer (P : Set G)).subtype) hcc
      rw [hmapP, Subgroup.map_commutator, hmapP, Subgroup.map_subgroupOf_eq_of_le hVL] at h
      exact h.symm
    ·
      exact Odd.of_dvd_nat (Odd.of_dvd_nat hG.odd (Subgroup.card_subgroup_dvd_card V))
        (by rw [← Subgroup.index_eq_card]; exact Subgroup.index_dvd_card _)
    ·
      intro hdvd
      exact hVp (hdvd.trans (by rw [← Subgroup.index_eq_card]; exact Subgroup.index_dvd_card _))

end

end CFSG.FeitThompson.Proofs
