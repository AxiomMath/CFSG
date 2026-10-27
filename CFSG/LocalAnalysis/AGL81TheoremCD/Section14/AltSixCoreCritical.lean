module

public import Mathlib.GroupTheory.IsPerfect

import CFSG.GH74.GLS.Stage2.Signalizer.L53Basic
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.AltSixCoreClassTwo
import CFSG.RankThree.PartTwo.Sec13.Item135CritProof
import TauCeti.GroupTheory.OrderOfElement.PPart

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A6Core

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem centralizes_of_coprime_of_centralizes_center {p : ℕ} [Fact p.Prime] {D : Subgroup G}
    (hDp : IsPGroup p ↥D) {y : G} (hnotdvd : ¬ p ∣ orderOf y)
    (hZ : ∀ z ∈ D ⊓ centralizer (D : Set G), ⁅z, y⁆ = 1)
    (hD : ∀ x ∈ D, ⁅x, y⁆ ∈ D ⊓ centralizer (D : Set G)) :
    ∀ x ∈ D, y * x * y⁻¹ = x := by
  have hZconj : ∀ z ∈ D ⊓ centralizer (D : Set G), y * z * y⁻¹ = z := by
    intro z hz
    have h2 : z * y = y * z := commutatorElement_eq_one_iff_mul_comm.mp (hZ z hz)
    calc y * z * y⁻¹ = (z * y) * y⁻¹ := by rw [← h2]
      _ = z := by group
  refine CFSG.GH74.GLS.Stage2.Signalizer.L53.centralizes_of_coprime hDp inf_le_left
    hnotdvd hZconj ?_
  intro x hx
  have hk := hD x hx
  have hcomm : Commute x ⁅x, y⁆ := Subgroup.mem_centralizer_iff.mp hk.2 x hx
  have hconj : y * x * y⁻¹ = ⁅x, y⁆⁻¹ * x := by
    rw [commutatorElement_def]
    group
  have hconv : x⁻¹ * (⁅x, y⁆⁻¹ * x) = ⁅x, y⁆⁻¹ := by
    rw [← mul_assoc, (hcomm.inv_left.inv_right).eq, mul_assoc, inv_mul_cancel, mul_one]
  rw [hconj, hconv]
  exact (D ⊓ centralizer (D : Set G)).inv_mem hk

private def conjAct {R Y : Subgroup G} (hYR : Y ≤ normalizer (R : Set G)) :
    ↥Y →* MulAut ↥R :=
  R.normalizerMonoidHom.comp (Subgroup.inclusion hYR)

private theorem conjAct_apply {R Y : Subgroup G} (hYR : Y ≤ normalizer (R : Set G))
    (y : ↥Y) (x : ↥R) :
    ((conjAct hYR y) x : G) = (y : G) * (x : G) * (y : G)⁻¹ := rfl

private theorem isPGroup_range_conjAct {p : ℕ} [Fact p.Prime] {R Y : Subgroup G}
    (hYR : Y ≤ normalizer (R : Set G))
    (hcop : ∀ y ∈ Y, Nat.Coprime (orderOf y) p → ∀ x ∈ R, y * x * y⁻¹ = x) :
    IsPGroup p (conjAct hYR).range := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨z, hz⟩
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hz
  have hy0 : orderOf (y : G) ≠ 0 := (orderOf_pos (y : G)).ne'
  let q : G := TauCeti.pFreePart p (y : G)
  let yp : ↥Y := ⟨TauCeti.pPart p (y : G),
    Subgroup.zpowers_le.mpr y.2 (TauCeti.pPart_mem_zpowers p (y : G))⟩
  have hqY : q ∈ Y :=
    Subgroup.zpowers_le.mpr y.2 (TauCeti.pFreePart_mem_zpowers p (y : G))
  have hqcop : Nat.Coprime (orderOf q) p :=
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr
      (TauCeti.not_dvd_orderOf_pFreePart Fact.out hy0)).symm
  have hqcent : ∀ x ∈ R, q * x * q⁻¹ = x := hcop q hqY hqcop
  have hφeq : conjAct hYR y = conjAct hYR yp := by
    ext x
    rw [conjAct_apply, conjAct_apply]
    rw [show (y : G) = TauCeti.pPart p (y : G) * q from
      (TauCeti.pPart_mul_pFreePart p (y : G)).symm]
    calc (TauCeti.pPart p (y : G) * q) * (x : G) *
          (TauCeti.pPart p (y : G) * q)⁻¹
        = TauCeti.pPart p (y : G) * (q * (x : G) * q⁻¹) *
            (TauCeti.pPart p (y : G))⁻¹ := by group
      _ = TauCeti.pPart p (y : G) * (x : G) * (TauCeti.pPart p (y : G))⁻¹ := by
            rw [hqcent x x.2]
  have hdvd : orderOf ((conjAct hYR) y) ∣ p ^ (orderOf (y : G)).factorization p := by
    rw [hφeq]
    refine (orderOf_map_dvd (conjAct hYR) yp).trans ?_
    rw [Subgroup.orderOf_mk, TauCeti.orderOf_pPart Fact.out hy0]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
  exact ⟨k, (Subgroup.orderOf_mk ((conjAct hYR) y) hz).trans hk⟩

private theorem commutator_mem_inf_centralizer_of_map {R : Subgroup G} {Ω : Subgroup ↥R}
    (hcomm : ⁅Ω, ⊤⁆ ≤ Ω ⊓ centralizer (Ω : Set ↥R)) :
    ∀ x ∈ Ω.map R.subtype, ∀ y ∈ Ω.map R.subtype,
      ⁅x, y⁆ ∈ Ω.map R.subtype ⊓ centralizer (Ω.map R.subtype : Set G) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have hk : ⁅a, b⁆ ∈ Ω ⊓ centralizer (Ω : Set ↥R) :=
    hcomm (Subgroup.commutator_mem_commutator ha (Subgroup.mem_top b))
  have hkD : R.subtype ⁅a, b⁆ ∈ Ω.map R.subtype := Subgroup.mem_map_of_mem R.subtype hk.1
  have hkC : R.subtype ⁅a, b⁆ ∈ centralizer (Ω.map R.subtype : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hz
    exact congrArg R.subtype (Subgroup.mem_centralizer_iff.mp hk.2 c hc)
  simpa only [map_commutatorElement] using
    (show R.subtype ⁅a, b⁆ ∈ Ω.map R.subtype ⊓
      centralizer (Ω.map R.subtype : Set G) from ⟨hkD, hkC⟩)

private theorem normalizer_le_normalizer_inf_centralizer {R : Subgroup G} {Ω : Subgroup ↥R}
    (hchar : Ω.Characteristic) :
    normalizer (R : Set G) ≤
      normalizer ((Ω.map R.subtype ⊓ centralizer (Ω.map R.subtype : Set G) : Subgroup G) :
        Set G) := by
  haveI : Ω.Characteristic := hchar
  have hZeq := map_center_subtype_eq_inf_centralizer (Ω.map R.subtype)
  rw [← hZeq]
  exact (CFSG.normalizer_le_normalizer_image_of_characteristic R Ω).trans
    (CFSG.normalizer_le_normalizer_image_of_characteristic (Ω.map R.subtype)
      (Subgroup.center ↥(Ω.map R.subtype)))

theorem le_centralizer_of_commutator_eq_of_coprime {p : ℕ} [Fact p.Prime] {R Y : Subgroup G}
    (hYR : Y ≤ normalizer (R : Set G)) (hY : ⁅Y, Y⁆ = Y)
    (hcop : ∀ y ∈ Y, Nat.Coprime (orderOf y) p → ∀ x ∈ R, y * x * y⁻¹ = x) :
    Y ≤ centralizer (R : Set G) := by
  classical
  let φ : ↥Y →* MulAut ↥R := conjAct hYR
  haveI hperf : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hY
  haveI hperf' : Group.IsPerfect ↥φ.range := by
    have h := Group.IsPerfect.map (H := (⊤ : Subgroup ↥Y)) φ
    rwa [Subgroup.map_top] at h
  have hPp : IsPGroup p φ.range := isPGroup_range_conjAct hYR hcop
  have hbot : φ.range = ⊥ := by
    by_contra hne
    haveI : Nontrivial ↥φ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isNilpotent ↥φ.range hPp.isNilpotent
  have hbot' : Subgroup.map φ (⊤ : Subgroup ↥Y) = ⊥ := by
    simpa [Subgroup.map_top] using hbot
  have hker : (⊤ : Subgroup ↥Y) ≤ φ.ker :=
    (Subgroup.map_eq_bot_iff (⊤ : Subgroup ↥Y)).mp hbot'
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 : φ ⟨y, hy⟩ = 1 := MonoidHom.mem_ker.mp (hker (Subgroup.mem_top _))
  have h2 := congrArg (fun f : MulAut ↥R => ((f ⟨x, hx⟩ : ↥R) : G)) h1
  simp only [MulAut.one_apply] at h2
  have h2' : y * x * y⁻¹ = x := by
    rw [← conjAct_apply hYR ⟨y, hy⟩ ⟨x, hx⟩]
    exact h2
  calc x * y = (y * x * y⁻¹) * y := by rw [h2']
    _ = y * x := by group

theorem exists_critical_reduction {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {R : Subgroup G}
    (hR : IsPGroup p R) :
    ∃ D : Subgroup G, D ≤ R ∧ normalizer (R : Set G) ≤ normalizer (D : Set G) ∧
      normalizer (R : Set G) ≤
        normalizer (((D ⊓ centralizer (D : Set G) : Subgroup G)) : Set G) ∧
      (∀ x ∈ D, x ^ p = 1) ∧ (∀ x ∈ D, ∀ y ∈ D, ⁅x, y⁆ ∈ D ⊓ centralizer (D : Set G)) ∧
      ∀ Y : Subgroup G, Y ≤ normalizer (R : Set G) → ⁅Y, Y⁆ = Y →
        (∀ y ∈ Y, ∀ z ∈ D ⊓ centralizer (D : Set G), ⁅z, y⁆ = 1) →
        (∀ y ∈ Y, ∀ x ∈ D, ⁅x, y⁆ ∈ D ⊓ centralizer (D : Set G)) →
        Y ≤ centralizer (R : Set G) := by
  classical
  obtain ⟨C, -, -, -, -, hchar, -, hcomm, hexp, hfix, -⟩ :=
    CFSG.RankThree.PartTwo.Sec13.CritProof.exists_isThompsonCritical_omega
      (P := ↥R) hp2 hR
  let Ω : Subgroup ↥R := CFSG.RankThree.PartTwo.Sec13.CritProof.omegaOneIn p C
  let D : Subgroup G := Ω.map R.subtype
  have hDR : D ≤ R := Subgroup.map_subtype_le Ω
  haveI : Ω.Characteristic := hchar
  have hND : normalizer (R : Set G) ≤ normalizer (D : Set G) :=
    CFSG.normalizer_le_normalizer_image_of_characteristic R Ω
  have hNZ : normalizer (R : Set G) ≤
      normalizer ((D ⊓ centralizer (D : Set G) : Subgroup G) : Set G) :=
    normalizer_le_normalizer_inf_centralizer hchar
  have hDexp : ∀ x ∈ D, x ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    simpa using congrArg R.subtype (hexp y hy)
  have hDclass : ∀ x ∈ D, ∀ y ∈ D, ⁅x, y⁆ ∈ D ⊓ centralizer (D : Set G) :=
    commutator_mem_inf_centralizer_of_map hcomm
  refine ⟨D, hDR, hND, hNZ, hDexp, hDclass, ?_⟩
  intro Y hYR hY hYZ hYD
  apply le_centralizer_of_commutator_eq_of_coprime (p := p) hYR hY
  intro y hy hcop
  have hDp : IsPGroup p ↥D := hR.to_le hDR
  have hnotdvd : ¬ p ∣ orderOf y := (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcop.symm
  have hDcent : ∀ x ∈ D, y * x * y⁻¹ = x :=
    centralizes_of_coprime_of_centralizes_center hDp hnotdvd
      (fun z hz => hYZ y hy z hz) (hYD y hy)
  exact CFSG.RankThree.PartTwo.Sec13.CritProof.centralizes_of_coprime_of_fixing
    (Q := R) (D₀ := (Ω : Set ↥R)) hfix (hYR hy) hcop
    (fun d hd => hDcent (R.subtype d) (Subgroup.mem_map_of_mem R.subtype hd))

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A6Core
