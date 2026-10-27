module

public import CFSG.FeitThompson.Definitions.MaximalANormalizedQSubgroups
public import CFSG.FeitThompson.Definitions.LocalComplementaryPrimeConstraint
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Local.ConstrainedCentralizerCoreCoverage
import CFSG.FeitThompson.Local.InvariantHallPiSubgroupExtension
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.PGroupNormalizerCondition

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {q : ℕ}

private theorem le_of_subgroupOf_le_left {L X Y : Subgroup G} (hXL : X ≤ L)
    (h : X.subgroupOf L ≤ Y.subgroupOf L) : X ≤ Y := by
  have h2 := Subgroup.map_mono (f := L.subtype) h
  rw [Subgroup.map_subgroupOf_eq_of_le hXL, Subgroup.subgroupOf_map_subtype] at h2
  exact h2.trans inf_le_left

private theorem subgroupOf_map_subtype_self {L : Subgroup G} (S : Subgroup L) :
    (S.map L.subtype).subgroupOf L = S := by
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]

variable [Finite G]

theorem exists_isPGroup_ge_le_normalizer_not_dvd_index {D P Q : Subgroup G}
    (hsolv : Group.IsSolvable ((D ⊔ P : Subgroup G))) (hPD : P ≤ normalizer (D : Set G))
    (hcop : (Nat.card D).Coprime (Nat.card P)) (hq : q.Prime) (hQD : Q ≤ D)
    (hPQ : P ≤ normalizer (Q : Set G)) (hQq : IsPGroup q Q) :
    ∃ S : Subgroup G, S ≤ D ∧ IsPGroup q S ∧ Q ≤ S ∧ P ≤ normalizer (S : Set G) ∧
      ¬ q ∣ (S.subgroupOf D).index := by
  set L : Subgroup G := D ⊔ P with hL
  have hDL : D ≤ L := le_sup_left
  have hPL : P ≤ L := le_sup_right
  have hQL : Q ≤ L := hQD.trans hDL
  have : Group.IsSolvable L := hsolv
  have hDn : ((D.subgroupOf L)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDL).2 (sup_le Subgroup.le_normalizer hPD)
  have hKA : D.subgroupOf L ⊔ P.subgroupOf L = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hDL hPL, hL, Subgroup.subgroupOf_self]
  have hcop' : (Nat.card (D.subgroupOf L)).Coprime (Nat.card (P.subgroupOf L)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv]
    exact hcop
  have hQq' : IsPGroup q (Q.subgroupOf L) := hQq.comap_of_injective _ L.subtype_injective
  have hQD' : Q.subgroupOf L ≤ D.subgroupOf L := Subgroup.comap_mono hQD
  have hPQ' : P.subgroupOf L ≤ normalizer ((Q.subgroupOf L : Subgroup L) : Set L) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hQL]; exact Subgroup.comap_mono hPQ
  obtain ⟨S, hSD, hSHall, hQS, hPS⟩ :=
    exists_isHallSubgroup_subgroupOf_ge_le_normalizer hKA hcop' ({q} : Set ℕ) hQD'
      (isPiSubgroup_iff_isPiNumber.1 ((isPiSubgroup_singleton_iff hq _).2 hQq')) hPQ'
  have hcard : Nat.card (S.subgroupOf (D.subgroupOf L)) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSD).toEquiv
  have hmapD : (S.map L.subtype) ≤ D := by
    have h := Subgroup.map_mono (f := L.subtype) hSD
    rwa [Subgroup.map_subgroupOf_eq_of_le hDL] at h
  refine ⟨S.map L.subtype, hmapD, ?_, ?_, ?_, ?_⟩
  · refine (isPiSubgroup_singleton_iff hq _).1 (isPiSubgroup_iff_isPiNumber.2 ?_)
    rw [Subgroup.card_map_of_injective L.subtype_injective, ← hcard]
    exact hSHall.natCard
  · have h := Subgroup.map_mono (f := L.subtype) hQS
    rwa [Subgroup.map_subgroupOf_eq_of_le hQL] at h
  · refine le_of_subgroupOf_le_left hPL ?_
    rw [Subgroup.subgroupOf_normalizer_eq (hmapD.trans hDL), subgroupOf_map_subtype_self]
    exact hPS
  · intro hdvd
    have hidx : (S.subgroupOf (D.subgroupOf L)).index
        = ((S.map L.subtype).subgroupOf D).index := by
      have h1 : (S.subgroupOf (D.subgroupOf L)).index
          = ((S.map L.subtype).subgroupOf L).relIndex (D.subgroupOf L) := by
        rw [subgroupOf_map_subtype_self]; rfl
      rw [h1, Subgroup.relIndex_subgroupOf hDL]
      rfl
    exact isPiNumber_iff.1 hSHall.index q (by
      rw [hidx]
      exact Nat.mem_primeFactors.2 ⟨hq, hdvd, Subgroup.index_ne_zero_of_finite⟩) rfl

omit [Finite G] in
theorem le_of_isPGroup_of_not_dvd_index {D S T : Subgroup G} (hq : q.Prime)
    (hTD : T ≤ D) (hS : IsPGroup q S) (hT : IsPGroup q T)
    (hidx : ¬ q ∣ (S.subgroupOf D).index) (hST : S ≤ T) : T ≤ S := by
  have := Fact.mk hq
  have hS' : IsPGroup q (S.subgroupOf D) := hS.comap_of_injective _ D.subtype_injective
  have hT' : IsPGroup q (T.subgroupOf D) := hT.comap_of_injective _ D.subtype_injective
  have h := (hS'.toSylow hidx).is_maximal' hT'
    (by rw [IsPGroup.toSylow_coe]; exact Subgroup.comap_mono hST)
  rw [IsPGroup.toSylow_coe] at h
  exact le_of_subgroupOf_le_left hTD h.le

theorem mem_maximalNormalizedPSubgroups_of_mem_of_isPiSubgroup [IsSimpleGroup G]
    (hG : ¬ IsMulCommutative G) (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    {A P Q : Subgroup G} (hcon : IsConstrained A) (hq : q.Prime)
    (hqπ : q ∉ subgroupPrimeSupport A) (hAP : A ≤ P)
    (hP : IsPiSubgroup (subgroupPrimeSupport A) P) (hQbot : Q ≠ ⊥)
    (hQ : Q ∈ maximalNormalizedPSubgroups P q) : Q ∈ maximalNormalizedPSubgroups A q := by
  have hQq : IsPGroup q Q := isPGroup_of_mem hQ
  have hPQ : P ≤ normalizer (Q : Set G) := le_normalizer_of_mem hQ
  have hAQ : A ≤ normalizer (Q : Set G) := hAP.trans hPQ
  refine mem_maximalNormalizedPSubgroups_of_forall hQq hAQ fun R hRq hAR hQR => ?_
  set H : Subgroup G := normalizer (Q : Set G) with hH
  have hHtop : H < ⊤ := normalizer_lt_top_of_isPGroup hG hq hQbot hQq
  have hQH : Q ≤ H := Subgroup.le_normalizer
  have hARH : A ≤ normalizer ((R ⊓ H : Subgroup G) : Set G) :=
    le_trans (le_inf hAR (hAQ.trans Subgroup.le_normalizer))
      Subgroup.inf_normalizer_le_normalizer_inf
  have hRHπ : IsPiSubgroup (subgroupPrimeSupportCompl A) (R ⊓ H : Subgroup G) :=
    ((isPiSubgroup_singleton_iff hq _).2 hRq.to_inf_left).mono
      (Set.singleton_subset_iff.2 (mem_subgroupPrimeSupportCompl_iff.2 ⟨hq, hqπ⟩))
  set D : Subgroup G := (piCore (subgroupPrimeSupportCompl A) H).map H.subtype with hD
  have hRHD : (R ⊓ H : Subgroup G) ≤ D := hcon.le_map_piCore hHtop hAQ inf_le_right hRHπ hARH
  have hQRH : Q ≤ (R ⊓ H : Subgroup G) := le_inf hQR hQH
  have hDH : D ≤ H := map_piCore_le _ _
  have hDPtop : (D ⊔ P : Subgroup G) ≠ ⊤ := fun h =>
    hHtop.ne (top_le_iff.1 (h.ge.trans (sup_le hDH hPQ)))
  have hcop : (Nat.card D).Coprime (Nat.card P) :=
    Nat.Coprime.symm (IsPiNumber.coprime_of_compl (isPiSubgroup_iff_isPiNumber.1 hP)
      (isPiSubgroup_iff_isPiNumber.1 ((isPiSubgroup_map_piCore _ _).mono
        fun _ hp => (mem_subgroupPrimeSupportCompl_iff.1 hp).2))
      Nat.card_pos.ne' Nat.card_pos.ne')
  obtain ⟨S, -, hSq, hQS, hPS, hSidx⟩ :=
    exists_isPGroup_ge_le_normalizer_not_dvd_index (hsolv _ hDPtop) (hPQ.trans
      (le_normalizer_map_piCore _ _)) hcop hq (hQRH.trans hRHD) hPQ hQq
  rw [eq_of_mem_of_le hQ hSq hPS hQS] at hSidx
  have hRHQ : (R ⊓ H : Subgroup G) = Q :=
    le_antisymm (le_of_isPGroup_of_not_dvd_index hq hRHD hQq hRq.to_inf_left hSidx hQRH) hQRH
  refine le_antisymm (Subgroup.subgroupOf_eq_top.1 ?_) hQR
  by_contra hne
  have := Fact.mk hq
  refine absurd ?_ (normalizerCondition_of_isPGroup (P := R) hRq _
    (lt_top_iff_ne_top.2 hne)).ne'
  rw [← Subgroup.subgroupOf_normalizer_eq hQR, ← hH, ← Subgroup.inf_subgroupOf_left H R, hRHQ]

theorem maximalNormalizedPSubgroups_subset_of_isPiSubgroup [IsSimpleGroup G]
    (hG : ¬ IsMulCommutative G) (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    {A P : Subgroup G} (hcon : IsConstrained A) (hq : q.Prime)
    (hqπ : q ∉ subgroupPrimeSupport A) (hAP : A ≤ P)
    (hP : IsPiSubgroup (subgroupPrimeSupport A) P) :
    maximalNormalizedPSubgroups P q \ {⊥} ⊆ maximalNormalizedPSubgroups A q := fun _ hQ =>
  mem_maximalNormalizedPSubgroups_of_mem_of_isPiSubgroup hG hsolv hcon hq hqπ hAP hP hQ.2 hQ.1

theorem mem_maximalNormalizedPSubgroups_of_mem_of_isPiSubgroup_of_odd
    (_hodd : Odd (Nat.card G)) (hsimple : IsSimpleGroup G) (hG : ¬ IsMulCommutative G)
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) {A P Q : Subgroup G}
    (_hAbot : ⊥ < A) (_hAtop : A < ⊤) (hcon : IsConstrained A) (hq : q.Prime)
    (hqπ : q ∉ subgroupPrimeSupport A) (hAP : A ≤ P)
    (hP : IsPiSubgroup (subgroupPrimeSupport A) P) (hQbot : Q ≠ ⊥)
    (hQ : Q ∈ maximalNormalizedPSubgroups P q) : Q ∈ maximalNormalizedPSubgroups A q :=
  have := hsimple
  mem_maximalNormalizedPSubgroups_of_mem_of_isPiSubgroup hG hsolv hcon hq hqπ hAP hP hQbot hQ

end

end CFSG.FeitThompson
