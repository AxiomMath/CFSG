module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

structure CInv (C : Type) [Group C] where
  z : C
  central : ∀ c : C, c * z = z * c
  sq : z ^ 2 = 1
  ne : z ≠ 1

namespace CInv

variable {C : Type} [Group C] (c : CInv C)

instance instNormal : (zpowers c.z).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hz : c.z ∈ Subgroup.center C := Subgroup.mem_center_iff.mpr c.central
  have hn' : n ∈ Subgroup.center C := (Subgroup.zpowers_le (H := Subgroup.center C)).mpr hz hn
  rw [Subgroup.mem_center_iff.mp hn' g, mul_assoc, mul_inv_cancel, mul_one]
  exact hn

abbrev Qt : Type := C ⧸ zpowers c.z

@[expose] def qmap : C →* c.Qt := QuotientGroup.mk' (zpowers c.z)

@[expose] def bar (S : Subgroup C) : Subgroup c.Qt := S.map c.qmap

theorem qmap_surjective : Function.Surjective c.qmap := by
  simpa only [qmap] using QuotientGroup.mk'_surjective (N := zpowers c.z)

theorem ker_qmap : c.qmap.ker = zpowers c.z := by
  simpa only [qmap] using QuotientGroup.ker_mk' (N := zpowers c.z)

theorem qmap_eq_one_iff {x : C} : c.qmap x = 1 ↔ x ∈ zpowers c.z := by
  rw [← MonoidHom.mem_ker, c.ker_qmap]

theorem card_zpowers : Nat.card (zpowers c.z) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime c.sq c.ne

theorem comap_bar {S : Subgroup C} (h : zpowers c.z ≤ S) : (c.bar S).comap c.qmap = S := by
  have hk : c.qmap.ker ≤ S := by rw [c.ker_qmap]; exact h
  change (S.map c.qmap).comap c.qmap = S
  exact Subgroup.comap_map_eq_self hk

theorem qmap_mem_bar_iff {S : Subgroup C} (h : zpowers c.z ≤ S) {x : C} :
    c.qmap x ∈ c.bar S ↔ x ∈ S := by
  rw [← Subgroup.mem_comap, c.comap_bar h]

theorem bar_comap (U : Subgroup c.Qt) : c.bar (U.comap c.qmap) = U := by
  change (U.comap c.qmap).map c.qmap = U
  exact Subgroup.map_comap_eq_self_of_surjective c.qmap_surjective U

theorem bar_mono {S T : Subgroup C} (h : S ≤ T) : c.bar S ≤ c.bar T := by
  change S.map c.qmap ≤ T.map c.qmap
  exact Subgroup.map_mono h

theorem card_bar {S : Subgroup C} (h : zpowers c.z ≤ S) :
    Nat.card ↥S = 2 * Nat.card ↥(c.bar S) := by
  have hker : Nat.card ((zpowers c.z).subgroupOf S) = 2 := by
    rw [← Subgroup.card_map_of_injective S.subtype_injective
        (K := (zpowers c.z).subgroupOf S),
      Subgroup.map_subgroupOf_eq_of_le h, c.card_zpowers]
  have hcard := Subgroup.card_ker_mul_card_range (c.qmap.domRestrict S)
  rw [MonoidHom.ker_domRestrict, c.ker_qmap, MonoidHom.domRestrict_range, hker] at hcard
  change Nat.card ↥S = 2 * Nat.card ↥(S.map c.qmap)
  exact hcard.symm

theorem card_comap (U : Subgroup c.Qt) : Nat.card ↥(U.comap c.qmap) = 2 * Nat.card ↥U := by
  have h : zpowers c.z ≤ U.comap c.qmap := by
    rw [Subgroup.zpowers_le, Subgroup.mem_comap,
      c.qmap_eq_one_iff.mpr (Subgroup.mem_zpowers c.z)]
    exact U.one_mem
  have hc := c.card_bar h
  rwa [c.bar_comap U] at hc

theorem bar_commutator (S T : Subgroup C) : c.bar ⁅S, T⁆ = ⁅c.bar S, c.bar T⁆ := by
  change (⁅S, T⁆).map c.qmap = ⁅S.map c.qmap, T.map c.qmap⁆
  exact Subgroup.map_commutator S T c.qmap

theorem bar_perfect {Y : Subgroup C} (hY : ⁅Y, Y⁆ = Y) : ⁅c.bar Y, c.bar Y⁆ = c.bar Y := by
  rw [← c.bar_commutator Y Y, hY]

theorem isPGroup_bar {S : Subgroup C} (hS : IsPGroup 2 ↥S) : IsPGroup 2 ↥(c.bar S) := by
  change IsPGroup 2 ↥(S.map c.qmap)
  have h := hS.of_surjective ((c.qmap.domRestrict S).rangeRestrict)
    ((c.qmap.domRestrict S).rangeRestrict_surjective)
  rwa [MonoidHom.domRestrict_range] at h

theorem isPGroup_comap [Finite C] {U : Subgroup c.Qt} (hU : IsPGroup 2 ↥U) :
    IsPGroup 2 ↥(U.comap c.qmap) := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥U)).mp hU
  exact (IsPGroup.iff_card (p := 2) (G := ↥(U.comap c.qmap))).mpr
    ⟨n + 1, by rw [c.card_comap U, hn, pow_succ, mul_comm]⟩

end CInv

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
