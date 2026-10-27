module

public import CFSG.FeitThompson.Local.ConstrainedCentralizerCoreCoverage
import Mathlib.Data.Rat.Floor

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] [Finite G] {A P : Subgroup G}

theorem subgroupPrimeSupport_eq_of_isPiSubgroup (hAP : A ≤ P)
    (hP : IsPiSubgroup (subgroupPrimeSupport A) P) :
    subgroupPrimeSupport P = subgroupPrimeSupport A := by
  refine Set.Subset.antisymm (fun p hp => isPiSubgroup_iff.1 hP p
    (mem_subgroupPrimeSupport_iff.1 hp)) fun p hp => ?_
  exact mem_subgroupPrimeSupport_iff.2 (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hAP)
    Nat.card_pos.ne' (mem_subgroupPrimeSupport_iff.1 hp))

theorem subgroupPrimeSupportCompl_eq_of_isPiSubgroup (hAP : A ≤ P)
    (hP : IsPiSubgroup (subgroupPrimeSupport A) P) :
    subgroupPrimeSupportCompl P = subgroupPrimeSupportCompl A := by
  ext q
  rw [mem_subgroupPrimeSupportCompl_iff, mem_subgroupPrimeSupportCompl_iff,
    subgroupPrimeSupport_eq_of_isPiSubgroup hAP hP]

theorem IsConstrained.of_le_of_isPiSubgroup (hA : IsConstrained A) (hAP : A ≤ P)
    (hP : IsPiSubgroup (subgroupPrimeSupport A) P) : IsConstrained P := by
  rw [isConstrained_iff]
  intro H hH hPH Y hYH hY hN
  rw [subgroupPrimeSupportCompl_eq_of_isPiSubgroup hAP hP] at hY ⊢
  exact hA.le_map_piCore hH (hAP.trans hPH) hYH hY (hAP.trans hN)

theorem constrainedCentralizerCore_eq_inf_centralizer [IsSimpleGroup G]
    (hAbot : ⊥ < A) (hAtop : A < ⊤) (hcon : IsConstrained A) (hAP : A ≤ P)
    (hP : IsPiSubgroup (subgroupPrimeSupport A) P) :
    constrainedCentralizerCore P = constrainedCentralizerCore A ⊓ centralizer (P : Set G) := by
  have hcompl := subgroupPrimeSupportCompl_eq_of_isPiSubgroup hAP hP
  have hCPA : centralizer (P : Set G) ≤ centralizer (A : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hAP)
  refine le_antisymm (le_inf ?_ (constrainedCentralizerCore_le_centralizer P)) ?_
  · refine le_constrainedCentralizerCore_of_isConstrained hAbot hAtop hcon
      ((constrainedCentralizerCore_le_centralizer P).trans hCPA) ?_
    have h := isPiSubgroup_constrainedCentralizerCore P
    rwa [hcompl] at h
  · refine le_constrainedCentralizerCore inf_le_right ?_ ?_
    · exact le_trans (le_inf
        (hCPA.trans (centralizer_le_normalizer_constrainedCentralizerCore A))
          Subgroup.le_normalizer) Subgroup.inf_normalizer_le_normalizer_inf
    · rw [hcompl]
      exact (isPiSubgroup_constrainedCentralizerCore A).of_le inf_le_left

theorem mem_constrainedCentralizerCore_iff_of_le_of_isPiSubgroup [IsSimpleGroup G]
    (hAbot : ⊥ < A) (hAtop : A < ⊤) (hcon : IsConstrained A) (hAP : A ≤ P)
    (hP : IsPiSubgroup (subgroupPrimeSupport A) P) {x : G} :
    x ∈ constrainedCentralizerCore P ↔
      x ∈ constrainedCentralizerCore A ∧ ∀ p ∈ P, x * p = p * x := by
  rw [constrainedCentralizerCore_eq_inf_centralizer hAbot hAtop hcon hAP hP, Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff]
  exact and_congr_right fun _ => ⟨fun h p hp => (h p hp).symm, fun h p hp => (h p hp).symm⟩

end

end CFSG.FeitThompson
