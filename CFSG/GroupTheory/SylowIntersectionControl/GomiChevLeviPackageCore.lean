module

import CFSG.GroupTheory.CommutatorPreimageCenter
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.OpCoreSylow
public import CFSG.Assembly.Defs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.ABGLocalTools CFSG.LieType.BorelTits Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {L U P D : Subgroup G}

@[expose] def IsGomiLeviCore (P D : Subgroup G) : Prop :=
  ∀ x : G, x ∈ D ↔ x ∈ P ∧ ∀ p ∈ P, ⁅x, p⁆ ∈ pCoreOf 2 P

theorem exists_isGomiLeviCore (P : Subgroup G) : ∃ D : Subgroup G, IsGomiLeviCore P D :=
  exists_subgroup_mem_iff_commutator_mem (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)

theorem IsGomiLeviCore.le (hD : IsGomiLeviCore P D) : D ≤ P := fun x hx => ((hD x).1 hx).1

private lemma conj_mem_of_mem_normalizer {k x : G}
    (hk : k ∈ Subgroup.normalizer (P : Set G)) (hx : x ∈ P) : k * x * k⁻¹ ∈ P :=
  (Subgroup.mem_normalizer_iff.mp hk x).mp hx

private lemma conj_mem_pCoreOf_of_mem_normalizer {k x : G}
    (hk : k ∈ Subgroup.normalizer (P : Set G)) (hx : x ∈ pCoreOf 2 P) :
    k * x * k⁻¹ ∈ pCoreOf 2 P :=
  (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_pCoreOf 2 P hk) x).mp hx

theorem IsGomiLeviCore.pCoreOf_le (hD : IsGomiLeviCore P D) : pCoreOf 2 P ≤ D := by
  intro r hr
  rw [hD r]
  refine ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 P hr, fun p hp => ?_⟩
  have hpr : p * r * p⁻¹ ∈ pCoreOf 2 P :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 P hp) r).mp hr
  have hprinv : p * r⁻¹ * p⁻¹ ∈ pCoreOf 2 P := by
    simpa [mul_inv_rev, inv_inv, mul_assoc] using inv_mem hpr
  simpa only [commutatorElement_def, mul_assoc] using mul_mem hr hprinv

theorem IsGomiLeviCore.commutator_le (hD : IsGomiLeviCore P D) : ⁅D, P⁆ ≤ pCoreOf 2 P := by
  rw [Subgroup.commutator_le]
  intro x hx p hp
  exact ((hD x).1 hx).2 p hp

theorem IsGomiLeviCore.normalizer_le (hD : IsGomiLeviCore P D) :
    normalizer (P : Set G) ≤ normalizer (D : Set G) := by
  have hconj : ∀ k ∈ normalizer (P : Set G), ∀ y ∈ D, k * y * k⁻¹ ∈ D := by
    intro k hk y hy
    rw [hD] at hy ⊢
    refine ⟨conj_mem_of_mem_normalizer hk hy.1, fun p hp => ?_⟩
    rw [show ⁅k * y * k⁻¹, p⁆ = k * ⁅y, k⁻¹ * p * k⁆ * k⁻¹ by group]
    exact conj_mem_pCoreOf_of_mem_normalizer hk
      (hy.2 (k⁻¹ * p * k) (by simpa using conj_mem_of_mem_normalizer (inv_mem hk) hp))
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨hconj g hg x, fun hx => by
    have h := hconj g⁻¹ (inv_mem hg) (g * x * g⁻¹) hx
    have hx' : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [hx']
    simpa using h⟩

theorem IsGomiLeviCore.le_normalizer (hD : IsGomiLeviCore P D) :
    P ≤ normalizer (D : Set G) :=
  Subgroup.le_normalizer.trans hD.normalizer_le

theorem pCoreOf_le_of_isSylowOf_of_le [Finite G] (hU : IsSylowOf 2 U L) (hUP : U ≤ P)
    (hPL : P ≤ L) : pCoreOf 2 P ≤ U := by
  exact CFSG.LocalAnalysis.AGL81TheoremCD.Section12.pCoreOf_le_of_isSylowOf (hU.of_le hUP hPL)

theorem IsGomiLeviCore.le_inf_normalizer [Finite G] (hU : IsSylowOf 2 U L) (hUP : U ≤ P)
    (hPL : P ≤ L) (hD : IsGomiLeviCore P D) : D ≤ L ⊓ normalizer (U : Set G) := by
  have hRU : pCoreOf 2 P ≤ U := pCoreOf_le_of_isSylowOf_of_le hU hUP hPL
  have hconj : ∀ k ∈ D, ∀ y ∈ U, k * y * k⁻¹ ∈ U := by
    intro k hk y hy
    have hcomm : ⁅k, y⁆ ∈ pCoreOf 2 P := ((hD k).1 hk).2 y (hUP hy)
    have hkey : k * y * k⁻¹ = ⁅k, y⁆ * y := by group
    rw [hkey]
    exact mul_mem (hRU hcomm) hy
  intro x hx
  rw [Subgroup.mem_inf]
  refine ⟨hPL (hD.le hx), ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro u
  exact ⟨hconj x hx u, fun hu => by
    have hxu : u = x⁻¹ * (x * u * x⁻¹) * x := by group
    rw [hxu]
    simpa using hconj x⁻¹ (inv_mem hx) (x * u * x⁻¹) hu⟩

theorem IsGomiLeviCore.not_two_dvd_relIndex [Finite G] (hU : IsSylowOf 2 U L) (hUP : U ≤ P)
    (hPL : P ≤ L) (hD : IsGomiLeviCore P D) : ¬ 2 ∣ (pCoreOf 2 P).relIndex D := by
  have hR : pCoreOf 2 P ≤ D := hD.pCoreOf_le
  have hRU : pCoreOf 2 P ≤ U := pCoreOf_le_of_isSylowOf_of_le hU hUP hPL
  have hTD : IsSylowOf 2 (U ⊓ D) D :=
    (hU.of_le hUP hPL).inf_of_le_normalizer hD.le hD.le_normalizer
  have hconj : ∀ p ∈ P, ∀ t ∈ (U ⊓ D : Subgroup G), p * t * p⁻¹ ∈ U ⊓ D := by
    intro p hp t ht
    rw [Subgroup.mem_inf] at ht ⊢
    have hcomm : ⁅t, p⁆ ∈ pCoreOf 2 P := ((hD t).1 ht.2).2 p hp
    have hkey : p * t * p⁻¹ = ⁅t, p⁆⁻¹ * t := by group
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hD.le_normalizer hp) t).mp ht.2⟩
    rw [hkey]
    exact mul_mem (inv_mem (hRU hcomm)) ht.1
  have hTnorm : P ≤ Subgroup.normalizer ((U ⊓ D : Subgroup G) : Set G) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro t
    exact ⟨hconj p hp t, fun ht => by
      have h := hconj p⁻¹ (inv_mem hp) (p * t * p⁻¹) ht
      have hkey : t = p⁻¹ * (p * t * p⁻¹) * p := by group
      rw [hkey]
      simpa using h⟩
  have hTR : U ⊓ D = pCoreOf 2 P := le_antisymm
    (le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans hUP) hTnorm hTD.isPGroup) (le_inf hRU hR)
  rw [← hTR]
  exact (isSylowOf_iff.mp hTD).2.2

end CFSG.GroupTheory
