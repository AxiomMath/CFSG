module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.Config
public import Mathlib.GroupTheory.SpecificGroups.Alternating

import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Perm5
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Util.Perfect
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup
open scoped commutatorElement

namespace H2Cfg

variable {G : Type*} [Group G] {t v : G} {J : Subgroup G}

private theorem cfgJ_map_equiv {e : ↥J ≃* Equiv.Perm (Fin 5)} :
    (commutator ↥J).map e.toMonoidHom = alternatingGroup (Fin 5) := by
  change Subgroup.map e.toMonoidHom ⁅(⊤ : Subgroup ↥J), ⊤⁆ = alternatingGroup (Fin 5)
  rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective]
  exact alternatingGroup.commutator_perm_eq (α := Fin 5) (by simp)

private theorem cfgJ_derived_eq (cfg : H2Cfg G t v J) (e : ↥J ≃* Equiv.Perm (Fin 5)) :
    (⁅J, J⁆).subgroupOf J = (alternatingGroup (Fin 5)).comap e.toMonoidHom := by
  have hmap : (commutator ↥J).map J.subtype = ⁅J, J⁆ := Subgroup.map_subtype_commutator J
  have hemap : (commutator ↥J).map e.toMonoidHom = alternatingGroup (Fin 5) :=
    cfgJ_map_equiv (e := e)
  rw [← Subgroup.comap_subtype ⁅J, J⁆ J, ← hmap,
    Subgroup.comap_map_eq_self_of_injective J.subtype_injective (commutator ↥J), ← hemap,
    Subgroup.comap_map_eq_self_of_injective e.injective (commutator ↥J)]

private theorem cfgJ_derived_iso (cfg : H2Cfg G t v J) (e : ↥J ≃* Equiv.Perm (Fin 5)) :
    Nonempty (↥⁅J, J⁆ ≃* alternatingGroup (Fin 5)) := by
  refine ⟨?_⟩
  have hmap : (commutator ↥J).map J.subtype = ⁅J, J⁆ := Subgroup.map_subtype_commutator J
  have hemap : (commutator ↥J).map e.toMonoidHom = alternatingGroup (Fin 5) :=
    cfgJ_map_equiv (e := e)
  exact ((Subgroup.equivMapOfInjective (commutator ↥J) J.subtype J.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)).symm.trans
    ((Subgroup.equivMapOfInjective (commutator ↥J) e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hemap))

theorem card_J (cfg : H2Cfg G t v J) : Nat.card ↥J = 120 := by
  obtain ⟨e⟩ := cfg.J_iso
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
  decide

theorem derived_le (cfg : H2Cfg G t v J) : ⁅J, J⁆ ≤ J :=
  Subgroup.commutator_le_self J

theorem derived_le_centralizer (cfg : H2Cfg G t v J) : ⁅J, J⁆ ≤ centralizer ({t} : Set G) :=
  (derived_le cfg).trans cfg.J_le_centralizer

theorem derived_iso (cfg : H2Cfg G t v J) : Nonempty (↥⁅J, J⁆ ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := cfg.J_iso
  exact cfgJ_derived_iso cfg e

theorem derived_isSimple (cfg : H2Cfg G t v J) : IsSimpleGroup ↥⁅J, J⁆ := by
  obtain ⟨e⟩ := derived_iso cfg
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  exact e.isSimpleGroup

theorem derived_nonab (cfg : H2Cfg G t v J) : ∃ a ∈ ⁅J, J⁆, ∃ b ∈ ⁅J, J⁆, a * b ≠ b * a := by
  obtain ⟨e⟩ := derived_iso cfg
  obtain ⟨a, ha, b, hb, hab⟩ := rhyp_perm5.nonab
  refine ⟨e.symm ⟨a, ha⟩, (e.symm ⟨a, ha⟩).2, e.symm ⟨b, hb⟩, (e.symm ⟨b, hb⟩).2, ?_⟩
  intro h
  apply hab
  have hsub : e.symm ⟨a, ha⟩ * e.symm ⟨b, hb⟩ = e.symm ⟨b, hb⟩ * e.symm ⟨a, ha⟩ :=
    Subtype.ext h
  have h' := congrArg e hsub
  simpa using h'

theorem card_derived (cfg : H2Cfg G t v J) : Nat.card ↥⁅J, J⁆ = 60 := by
  obtain ⟨e⟩ := derived_iso cfg
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem derived_ne_bot (cfg : H2Cfg G t v J) : ⁅J, J⁆ ≠ ⊥ := by
  intro hbot
  have h := card_derived cfg
  rw [hbot, Subgroup.card_bot] at h
  norm_num at h

theorem derived_perfect (cfg : H2Cfg G t v J) : ⁅⁅J, J⁆, ⁅J, J⁆⁆ = ⁅J, J⁆ := by
  haveI : Group.IsPerfect ↥⁅J, J⁆ :=
    isPerfect_of_simple_of_nonab (derived_isSimple cfg) (derived_nonab cfg)
  exact Subgroup.commutator_eq_self

theorem not_isPGroup_derived (cfg : H2Cfg G t v J) : ¬ IsPGroup 2 ↥⁅J, J⁆ := by
  obtain ⟨e⟩ := cfg.J_iso
  haveI : Finite ↥J := Finite.of_injective e e.injective
  haveI : Finite ↥⁅J, J⁆ :=
    Finite.of_injective
      (fun x : ↥⁅J, J⁆ => (⟨x.1, Subgroup.commutator_le_self J x.2⟩ : ↥J))
      (fun x y h => by
        have : (x : G) = (y : G) := congrArg (fun z : ↥J => (z : G)) h
        exact Subtype.ext this)
  intro hP
  rw [isPGroup_iff_card_dvd_pow] at hP
  obtain ⟨n, hn⟩ := hP
  rw [card_derived cfg] at hn
  have h3 : 3 ∣ 2 ^ n := (by norm_num : (3 : ℕ) ∣ 60).trans hn
  have h32 : 3 ∣ (2 : ℕ) := Nat.prime_three.dvd_of_dvd_pow h3
  norm_num at h32

theorem derived_normalized (cfg : H2Cfg G t v J) {c : G} (hc : c ∈ centralizer ({t} : Set G))
    {x : G} (hx : x ∈ ⁅J, J⁆) : c * x * c⁻¹ ∈ ⁅J, J⁆ := by
  obtain ⟨a, ha, j, hj, rfl⟩ := cfg.exists_mul_of_mem_centralizer hc
  have hxJ : x ∈ J := derived_le cfg hx
  have hmem : j * x * j⁻¹ ∈ ⁅J, J⁆ := by
    have h1 : ⁅j, x⁆ ∈ ⁅J, J⁆ := Subgroup.commutator_mem_commutator hj hxJ
    have h2 : ⁅j, x⁆ * x ∈ ⁅J, J⁆ := mul_mem h1 hx
    have heq : j * x * j⁻¹ = ⁅j, x⁆ * x := conj_eq_commutatorElement_mul
    rwa [heq]
  have hyJ : j * x * j⁻¹ ∈ J := J.mul_mem (J.mul_mem hj hxJ) (J.inv_mem hj)
  have hay : a * (j * x * j⁻¹) = (j * x * j⁻¹) * a := cfg.comm a ha _ hyJ
  have hconj : (a * j) * x * (a * j)⁻¹ = j * x * j⁻¹ := by
    calc (a * j) * x * (a * j)⁻¹ = a * (j * x * j⁻¹) * a⁻¹ := by
          simp only [mul_inv_rev, mul_assoc]
      _ = (j * x * j⁻¹) := by rw [hay, mul_assoc, mul_inv_cancel, mul_one]
  rw [hconj]
  exact hmem

theorem eq_one_of_centralizes_derived (cfg : H2Cfg G t v J) {j : G} (hj : j ∈ J)
    (h : ∀ b ∈ ⁅J, J⁆, j * b = b * j) : j = 1 := by
  obtain ⟨e⟩ := cfg.J_iso
  have hder := cfgJ_derived_eq cfg e
  have key : e ⟨j, hj⟩ = 1 := by
    apply rhyp_perm5.eq_one_of_commute
    intro a ha
    have hmem : e.symm a ∈ (⁅J, J⁆).subgroupOf J := by
      rw [hder, Subgroup.mem_comap]
      simpa using ha
    have hmem' : ((e.symm a : ↥J) : G) ∈ ⁅J, J⁆ := Subgroup.mem_subgroupOf.mp hmem
    have hh := h ((e.symm a : ↥J) : G) hmem'
    have hh' : (⟨j, hj⟩ : ↥J) * e.symm a = e.symm a * ⟨j, hj⟩ := Subtype.ext hh
    have hcongr := congrArg e hh'
    simpa using hcongr
  have hone : (⟨j, hj⟩ : ↥J) = 1 := e.injective (by rw [key, map_one])
  simpa using congrArg Subtype.val hone

theorem derived_le_of_normal (cfg : H2Cfg G t v J) {M : Subgroup G} (hMJ : M ≤ J)
    (hM : ∀ j ∈ J, ∀ x ∈ M, j * x * j⁻¹ ∈ M) (hM1 : M ≠ ⊥) : ⁅J, J⁆ ≤ M := by
  obtain ⟨e⟩ := cfg.J_iso
  let N : Subgroup (Equiv.Perm (Fin 5)) := (M.subgroupOf J).map e.toMonoidHom
  have hNnormal : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rcases hn with ⟨m, hm, heq⟩
    obtain ⟨y, rfl⟩ := e.surjective g
    refine ⟨y * m * y⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.mpr ?_
      have hmM : (m : G) ∈ M := Subgroup.mem_subgroupOf.mp hm
      simpa using hM y.1 y.2 m.1 hmM
    · rw [← heq]
      simp only [map_mul, map_inv, MulEquiv.coe_toMonoidHom]
  have hNne : N ≠ ⊥ := by
    intro hN
    apply hM1
    rw [eq_bot_iff]
    intro x hxM
    have hxJ : x ∈ J := hMJ hxM
    have hxmem : (⟨x, hxJ⟩ : ↥J) ∈ M.subgroupOf J := Subgroup.mem_subgroupOf.mpr hxM
    have hxN : e ⟨x, hxJ⟩ ∈ N := ⟨⟨x, hxJ⟩, hxmem, rfl⟩
    rw [hN, Subgroup.mem_bot] at hxN
    have hone : (⟨x, hxJ⟩ : ↥J) = 1 := e.injective (by rw [hxN, map_one])
    simpa using congrArg Subtype.val hone
  have hmin := rhyp_perm5.min N hNnormal hNne
  intro x hx
  have hxJ : x ∈ J := derived_le cfg hx
  have hxsub : (⟨x, hxJ⟩ : ↥J) ∈ (⁅J, J⁆).subgroupOf J := Subgroup.mem_subgroupOf.mpr hx
  rw [cfgJ_derived_eq cfg e, Subgroup.mem_comap] at hxsub
  have hxN : e ⟨x, hxJ⟩ ∈ N := hmin (by simpa using hxsub)
  rcases hxN with ⟨y, hy, hyeq⟩
  have hyx : y = ⟨x, hxJ⟩ := e.injective hyeq
  exact Subgroup.mem_subgroupOf.mp (hyx ▸ hy)

end H2Cfg

end CFSG.EvenSporadicStandard.HSStd.InvCent
