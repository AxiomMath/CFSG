module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
public import CFSG.FeitThompson.Definitions.MaximalANormalizedQSubgroups
public import CFSG.FeitThompson.Local.ConstrainedCentralizerCoreCoverage
import CFSG.FeitThompson.Local.InvariantHallSubgroupsConjugate
import CFSG.FeitThompson.Local.InvariantHallPiSubgroupExtension

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise Subgroup

variable {G : Type*} [Group G] {q : ℕ} {π : Set ℕ}

private theorem le_of_subgroupOf_le_left {L X Y : Subgroup G} (hXL : X ≤ L)
    (h : X.subgroupOf L ≤ Y.subgroupOf L) : X ≤ Y := by
  have h2 := Subgroup.map_mono (f := L.subtype) h
  rw [Subgroup.map_subgroupOf_eq_of_le hXL, Subgroup.subgroupOf_map_subtype] at h2
  exact h2.trans inf_le_left

private theorem subgroupOf_map_subtype_self {L : Subgroup G} (S : Subgroup L) :
    (S.map L.subtype).subgroupOf L = S := by
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]

private theorem isHallSubgroup_subgroupOf_subgroupOf_iff [Finite G] {L D R : Subgroup G}
    (hDL : D ≤ L) (hRD : R ≤ D) :
    IsHallSubgroup π ((R.subgroupOf L).subgroupOf (D.subgroupOf L)) ↔
      IsHallSubgroup π (R.subgroupOf D) := by
  have hRL : R ≤ L := hRD.trans hDL
  have hle : R.subgroupOf L ≤ D.subgroupOf L := Subgroup.comap_mono hRD
  have e1 : Nat.card ((R.subgroupOf L).subgroupOf (D.subgroupOf L)) = Nat.card (R.subgroupOf L) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have e2 : Nat.card (R.subgroupOf L) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv
  have e3 : Nat.card (R.subgroupOf D) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRD).toEquiv
  have hindex : ((R.subgroupOf L).subgroupOf (D.subgroupOf L)).index = (R.subgroupOf D).index := by
    rw [index_subgroupOf, Subgroup.relIndex_subgroupOf hDL, ← index_subgroupOf]
  rw [isHallSubgroup_iff, isHallSubgroup_iff, e1, e2, e3, hindex]

theorem exists_isHallSubgroup_subgroupOf_ge_le_normalizer_of_le_normalizer [Finite G]
    {D A R : Subgroup G} (hsolv : Group.IsSolvable (D ⊔ A : Subgroup G))
    (hAD : A ≤ normalizer (D : Set G)) (hcop : (Nat.card D).Coprime (Nat.card A)) (π : Set ℕ)
    (hRD : R ≤ D) (hRπ : IsPiNumber π (Nat.card R)) (hAR : A ≤ normalizer (R : Set G)) :
    ∃ S : Subgroup G, S ≤ D ∧ IsHallSubgroup π (S.subgroupOf D) ∧ R ≤ S ∧
      A ≤ normalizer (S : Set G) := by
  set L : Subgroup G := D ⊔ A with hL
  have hDL : D ≤ L := le_sup_left
  have hAL : A ≤ L := le_sup_right
  have hRL : R ≤ L := hRD.trans hDL
  have : Group.IsSolvable L := hsolv
  have hDn : ((D.subgroupOf L)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDL).2 (sup_le Subgroup.le_normalizer hAD)
  have hKA : D.subgroupOf L ⊔ A.subgroupOf L = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hDL hAL, hL, Subgroup.subgroupOf_self]
  have hcop' : (Nat.card (D.subgroupOf L)).Coprime (Nat.card (A.subgroupOf L)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv]
    exact hcop
  have hRπ' : IsPiNumber π (Nat.card (R.subgroupOf L)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv]
  have hAR' : A.subgroupOf L ≤ normalizer ((R.subgroupOf L : Subgroup L) : Set L) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hRL]; exact Subgroup.comap_mono hAR
  obtain ⟨S, hSD, hSHall, hRS, hAS⟩ := exists_isHallSubgroup_subgroupOf_ge_le_normalizer
    hKA hcop' π (Subgroup.comap_mono hRD : R.subgroupOf L ≤ D.subgroupOf L) hRπ' hAR'
  have hmapD : S.map L.subtype ≤ D := by
    have h := Subgroup.map_mono (f := L.subtype) hSD
    rwa [Subgroup.map_subgroupOf_eq_of_le hDL] at h
  have hRS' : R.subgroupOf L ≤ S := hRS
  refine ⟨S.map L.subtype, hmapD, ?_, ?_, ?_⟩
  · rw [← isHallSubgroup_subgroupOf_subgroupOf_iff hDL hmapD, subgroupOf_map_subtype_self]
    exact hSHall
  · have h := Subgroup.map_mono (f := L.subtype) hRS'
    rwa [Subgroup.map_subgroupOf_eq_of_le hRL] at h
  · refine le_of_subgroupOf_le_left hAL ?_
    rw [Subgroup.subgroupOf_normalizer_eq (hmapD.trans hDL), subgroupOf_map_subtype_self]
    exact hAS

theorem exists_mem_inf_centralizer_conj_inv_smul_eq_of_le_normalizer [Finite G]
    {D A R₁ R₂ : Subgroup G} (hsolv : Group.IsSolvable (D ⊔ A : Subgroup G))
    (hAD : A ≤ normalizer (D : Set G)) (hcop : (Nat.card D).Coprime (Nat.card A))
    (hR₁D : R₁ ≤ D) (hR₂D : R₂ ≤ D)
    (hH₁ : IsHallSubgroup π (R₁.subgroupOf D)) (hH₂ : IsHallSubgroup π (R₂.subgroupOf D))
    (hA₁ : A ≤ normalizer (R₁ : Set G)) (hA₂ : A ≤ normalizer (R₂ : Set G)) :
    ∃ c ∈ D ⊓ centralizer (A : Set G), MulAut.conj c⁻¹ • R₁ = R₂ := by
  set L : Subgroup G := D ⊔ A with hL
  have hDL : D ≤ L := le_sup_left
  have hAL : A ≤ L := le_sup_right
  have : Group.IsSolvable L := hsolv
  have hDn : ((D.subgroupOf L)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDL).2 (sup_le Subgroup.le_normalizer hAD)
  have hKA : D.subgroupOf L ⊔ A.subgroupOf L = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hDL hAL, hL, Subgroup.subgroupOf_self]
  have hcop' : (Nat.card (D.subgroupOf L)).Coprime (Nat.card (A.subgroupOf L)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv]
    exact hcop
  have hA₁' : A.subgroupOf L ≤ normalizer ((R₁.subgroupOf L : Subgroup L) : Set L) := by
    rw [← Subgroup.subgroupOf_normalizer_eq (hR₁D.trans hDL)]; exact Subgroup.comap_mono hA₁
  have hA₂' : A.subgroupOf L ≤ normalizer ((R₂.subgroupOf L : Subgroup L) : Set L) := by
    rw [← Subgroup.subgroupOf_normalizer_eq (hR₂D.trans hDL)]; exact Subgroup.comap_mono hA₂
  obtain ⟨c, hc, hceq⟩ := exists_mem_inf_centralizer_conj_inv_smul_eq (K := D.subgroupOf L)
    (A := A.subgroupOf L) hKA hcop' (Subgroup.comap_mono hR₁D) (Subgroup.comap_mono hR₂D)
    ((isHallSubgroup_subgroupOf_subgroupOf_iff hDL hR₁D).2 hH₁)
    ((isHallSubgroup_subgroupOf_subgroupOf_iff hDL hR₂D).2 hH₂) hA₁' hA₂'
  rw [Subgroup.mem_inf] at hc
  refine ⟨(c : G), Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hc.1, ?_⟩, ?_⟩
  · exact Subgroup.mem_centralizer_iff.2 fun a ha =>
      congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hc.2 (⟨a, hAL ha⟩ : L)
        (Subgroup.mem_subgroupOf.2 ha))
  · simpa using conj_smul_eq_of_subgroupOf (V := L) (hR₁D.trans hDL) (hR₂D.trans hDL)
      (v := c⁻¹) hceq

theorem exists_mem_inf_exists_mem_maximalNormalizedPSubgroups [Finite G] [IsSimpleGroup G]
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) {A Q₁ Q₂ H : Subgroup G}
    (hAbot : ⊥ < A) (hAtop : A < ⊤) (hcon : IsConstrained A) (hq : q.Prime)
    (hqπ : q ∉ subgroupPrimeSupport A) (hQ₁ : Q₁ ∈ maximalNormalizedPSubgroups A q)
    (hQ₂ : Q₂ ∈ maximalNormalizedPSubgroups A q) (hHtop : H < ⊤) (hAH : A ≤ H) :
    ∃ h ∈ constrainedCentralizerCore A ⊓ H, ∃ Q₃ ∈ maximalNormalizedPSubgroups A q,
      MulAut.conj h⁻¹ • (Q₁ ⊓ H) ≤ (MulAut.conj h⁻¹ • Q₁) ⊓ Q₃ ∧ Q₂ ⊓ H ≤ Q₂ ⊓ Q₃ := by
  set D : Subgroup G := (piCore (subgroupPrimeSupportCompl A) H).map H.subtype with hD
  have hDH : D ≤ H := map_piCore_le _ _
  have hAD : A ≤ normalizer (D : Set G) := hAH.trans (le_normalizer_map_piCore _ _)
  have hDπ : IsPiSubgroup (subgroupPrimeSupportCompl A) D := isPiSubgroup_map_piCore _ _
  have key : ∀ Q : Subgroup G, Q ∈ maximalNormalizedPSubgroups A q →
      (Q ⊓ H : Subgroup G) ≤ D ∧ IsPiNumber ({q} : Set ℕ) (Nat.card (Q ⊓ H : Subgroup G)) ∧
        A ≤ normalizer ((Q ⊓ H : Subgroup G) : Set G) := by
    intro Q hQ
    have hQq : IsPGroup q (Q ⊓ H : Subgroup G) := (isPGroup_of_mem hQ).to_inf_left
    have hnorm : A ≤ normalizer ((Q ⊓ H : Subgroup G) : Set G) :=
      le_trans (le_inf (le_normalizer_of_mem hQ) (hAH.trans Subgroup.le_normalizer))
        Subgroup.inf_normalizer_le_normalizer_inf
    have hπ : IsPiSubgroup (subgroupPrimeSupportCompl A) (Q ⊓ H : Subgroup G) :=
      ((isPiSubgroup_singleton_iff hq _).2 hQq).mono
        (Set.singleton_subset_iff.2 (mem_subgroupPrimeSupportCompl_iff.2 ⟨hq, hqπ⟩))
    exact ⟨hcon.le_map_piCore hHtop hAH inf_le_right hπ hnorm,
      isPiSubgroup_iff_isPiNumber.1 ((isPiSubgroup_singleton_iff hq _).2 hQq), hnorm⟩
  obtain ⟨h₁D, h₁π, h₁n⟩ := key Q₁ hQ₁
  obtain ⟨h₂D, h₂π, h₂n⟩ := key Q₂ hQ₂
  have hDAsolv : Group.IsSolvable (D ⊔ A : Subgroup G) :=
    hsolv _ fun hEq => hHtop.ne (top_le_iff.1 (hEq.ge.trans (sup_le hDH hAH)))
  have hcop : (Nat.card D).Coprime (Nat.card A) :=
    (IsPiNumber.coprime_of_compl
      (isPiSubgroup_iff_isPiNumber.1 (isPiSubgroup_subgroupPrimeSupport A))
      (isPiSubgroup_iff_isPiNumber.1
        (hDπ.mono fun _ hp => (mem_subgroupPrimeSupportCompl_iff.1 hp).2))
      Nat.card_pos.ne' Nat.card_pos.ne').symm
  obtain ⟨R₁, hR₁D, hR₁Hall, hQ₁R₁, hAR₁⟩ :=
    exists_isHallSubgroup_subgroupOf_ge_le_normalizer_of_le_normalizer hDAsolv hAD hcop
      ({q} : Set ℕ) h₁D h₁π h₁n
  obtain ⟨R₂, hR₂D, hR₂Hall, hQ₂R₂, hAR₂⟩ :=
    exists_isHallSubgroup_subgroupOf_ge_le_normalizer_of_le_normalizer hDAsolv hAD hcop
      ({q} : Set ℕ) h₂D h₂π h₂n
  obtain ⟨c, hc, hceq⟩ := exists_mem_inf_centralizer_conj_inv_smul_eq_of_le_normalizer
    hDAsolv hAD hcop hR₁D hR₂D hR₁Hall hR₂Hall hAR₁ hAR₂
  rw [Subgroup.mem_inf] at hc
  have hzD : Subgroup.zpowers c ≤ D := Subgroup.zpowers_le.2 hc.1
  have hcK : c ∈ constrainedCentralizerCore A :=
    le_constrainedCentralizerCore_of_isConstrained hAbot hAtop hcon
      (Subgroup.zpowers_le.2 hc.2) (hDπ.of_le hzD) (Subgroup.mem_zpowers c)
  have hR₂q : IsPGroup q R₂ := by
    refine (isPiSubgroup_singleton_iff hq _).1 (isPiSubgroup_iff_isPiNumber.2 ?_)
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₂D).toEquiv]
    exact hR₂Hall.natCard
  obtain ⟨Q₃, hQ₃, hR₂Q₃⟩ := exists_mem_maximalNormalizedPSubgroups_ge hR₂q hAR₂
  refine ⟨c, Subgroup.mem_inf.2 ⟨hcK, hDH hc.1⟩, Q₃, hQ₃, le_inf ?_ ?_, le_inf inf_le_left ?_⟩
  · exact Subgroup.pointwise_smul_le_pointwise_smul_iff.2 inf_le_left
  · calc MulAut.conj c⁻¹ • (Q₁ ⊓ H : Subgroup G)
        ≤ MulAut.conj c⁻¹ • R₁ := Subgroup.pointwise_smul_le_pointwise_smul_iff.2 hQ₁R₁
      _ = R₂ := hceq
      _ ≤ Q₃ := hR₂Q₃
  · exact hQ₂R₂.trans hR₂Q₃

theorem exists_mem_inf_exists_mem_maximalNormalizedPSubgroups_of_odd [Finite G]
    (_hodd : Odd (Nat.card G)) (hsimple : IsSimpleGroup G) (_hG : ¬ IsMulCommutative G)
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) {A Q₁ Q₂ H : Subgroup G}
    (hAbot : ⊥ < A) (hAtop : A < ⊤) (hcon : IsConstrained A) (hq : q.Prime)
    (hqπ : q ∉ subgroupPrimeSupport A) (hQ₁ : Q₁ ∈ maximalNormalizedPSubgroups A q)
    (hQ₂ : Q₂ ∈ maximalNormalizedPSubgroups A q) (hHtop : H < ⊤) (hAH : A ≤ H) :
    ∃ h ∈ constrainedCentralizerCore A ⊓ H, ∃ Q₃ ∈ maximalNormalizedPSubgroups A q,
      MulAut.conj h⁻¹ • (Q₁ ⊓ H) ≤ (MulAut.conj h⁻¹ • Q₁) ⊓ Q₃ ∧ Q₂ ⊓ H ≤ Q₂ ⊓ Q₃ :=
  have := hsimple
  exists_mem_inf_exists_mem_maximalNormalizedPSubgroups hsolv hAbot hAtop hcon hq hqπ hQ₁ hQ₂
    hHtop hAH

end

end CFSG.FeitThompson
