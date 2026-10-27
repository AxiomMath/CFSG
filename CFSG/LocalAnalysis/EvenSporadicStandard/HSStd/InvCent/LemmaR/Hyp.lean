module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.ZMod.Defs

import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Shape

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup

structure RHyp (B : Type*) [Group B] (B₀ : Subgroup B) : Prop where
  normal : B₀.Normal
  simple : IsSimpleGroup ↥B₀
  nonab : ∃ a ∈ B₀, ∃ b ∈ B₀, a * b ≠ b * a
  min : ∀ N : Subgroup B, N.Normal → N ≠ ⊥ → B₀ ≤ N
  center : ∀ x : B, (∀ y, y * x = x * y) → x = 1

variable {B : Type*} [Group B] {B₀ : Subgroup B}

theorem RHyp.eq_one_of_commute (hR : RHyp B B₀) {x : B} (hx : ∀ a ∈ B₀, x * a = a * x) :
    x = 1 := by
  by_contra hx1
  have hCne : Subgroup.centralizer (B₀ : Set B) ≠ ⊥ := by
    intro hbot
    have hxmem : x ∈ Subgroup.centralizer (B₀ : Set B) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (hx a ha).symm
    rw [hbot, Subgroup.mem_bot] at hxmem
    exact hx1 hxmem
  have hCnormal : (Subgroup.centralizer (B₀ : Set B)).Normal := by
    haveI : B₀.Normal := hR.normal
    infer_instance
  have hle : B₀ ≤ Subgroup.centralizer (B₀ : Set B) := hR.min _ hCnormal hCne
  obtain ⟨a, ha, b, hb, hab⟩ := hR.nonab
  exact hab (by
    have hcomm : b ∈ Subgroup.centralizer (B₀ : Set B) := hle hb
    rw [Subgroup.mem_centralizer_iff] at hcomm
    exact hcomm a ha)

variable {G : Type*} [Group G] {t : G}

theorem snd_eq_one_of_central (hB : ∀ x : B, (∀ y, y * x = x * y) → x = 1)
    (ζ : ↥(centralizer ({t} : Set G)) ≃* Multiplicative (ZMod 2) × B) {d : G}
    (hd : d ∈ centralizer ({t} : Set G)) (hc : ∀ y ∈ centralizer ({t} : Set G), y * d = d * y) :
    (ζ ⟨d, hd⟩).2 = 1 := by
  refine hB (ζ ⟨d, hd⟩).2 fun b => ?_
  have hcomm : ζ.symm (1, b) * (⟨d, hd⟩ : ↥(centralizer ({t} : Set G))) =
      (⟨d, hd⟩ : ↥(centralizer ({t} : Set G))) * ζ.symm (1, b) :=
    Subtype.ext (hc (ζ.symm (1, b) : G) (ζ.symm (1, b)).2)
  have h2 : (1, b) * ζ ⟨d, hd⟩ = ζ ⟨d, hd⟩ * (1, b) := by
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg ζ hcomm
  simpa using congrArg Prod.snd h2

theorem snd_zz_eq_one (hB : ∀ x : B, (∀ y, y * x = x * y) → x = 1)
    (ζ : ↥(centralizer ({t} : Set G)) ≃* Multiplicative (ZMod 2) × B) :
    (ζ ⟨t, mem_centralizer_singleton_iff.2 rfl⟩).2 = 1 := by
  refine snd_eq_one_of_central hB ζ (mem_centralizer_singleton_iff.2 rfl) fun y hy => ?_
  exact mem_centralizer_singleton_iff.1 hy

theorem fst_zz_ne_one (hB : ∀ x : B, (∀ y, y * x = x * y) → x = 1) (ht1 : t ≠ 1)
    (ζ : ↥(centralizer ({t} : Set G)) ≃* Multiplicative (ZMod 2) × B) :
    (ζ ⟨t, mem_centralizer_singleton_iff.2 rfl⟩).1 ≠ 1 := by
  intro h1
  apply ht1
  have h3 : ζ ⟨t, mem_centralizer_singleton_iff.2 rfl⟩ = 1 :=
    Prod.ext h1 (snd_zz_eq_one hB ζ)
  have h4 : (⟨t, mem_centralizer_singleton_iff.2 rfl⟩ : ↥(centralizer ({t} : Set G))) = 1 :=
    ζ.injective (by rw [h3, map_one])
  simpa using congrArg Subtype.val h4

theorem mem_zpowers_of_snd_eq_one (ht1 : t ≠ 1)
    (hB : ∀ x : B, (∀ y, y * x = x * y) → x = 1)
    (ζ : ↥(centralizer ({t} : Set G)) ≃* Multiplicative (ZMod 2) × B) {d : G}
    (hd : d ∈ centralizer ({t} : Set G)) (h : (ζ ⟨d, hd⟩).2 = 1) : d ∈ zpowers t := by
  let dd : ↥(centralizer ({t} : Set G)) := ⟨d, hd⟩
  let zt : ↥(centralizer ({t} : Set G)) := ⟨t, mem_centralizer_singleton_iff.2 rfl⟩
  by_cases hg : (ζ dd).1 = 1
  · have h3 : ζ dd = 1 := Prod.ext hg (by simpa using h)
    have h4 : dd = 1 := ζ.injective (by rw [h3, map_one])
    have h5 : d = 1 := by simpa [dd] using congrArg Subtype.val h4
    rw [h5]
    exact Subgroup.one_mem _
  · have hz2' : (ζ zt).1 ≠ 1 := by
      simpa [zt] using fst_zz_ne_one (t := t) hB ht1 ζ
    have h3 : ζ dd = ζ zt :=
      Prod.ext (CFSG.EvenSporadicStandard.SolomonRed.z2_eq_of_ne_one hg hz2')
        (by rw [show (ζ dd).2 = 1 from h, show (ζ zt).2 = 1 from snd_zz_eq_one hB ζ])
    have h4 : dd = zt := ζ.injective h3
    have h5 : d = t := by simpa [dd, zt] using congrArg Subtype.val h4
    rw [h5]
    exact Subgroup.mem_zpowers t

end CFSG.EvenSporadicStandard.HSStd.InvCent
