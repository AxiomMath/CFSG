module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.KC.F4NA

open Subgroup

theorem card_le_of_conjs {G : Type*} [Group G] (S : Subgroup G) (hS : Nat.card S = 729)
    {x : G} (hx : x ∈ S) (us : List G) (hus : ∀ u ∈ us, u ∈ S)
    (hd : (us.map fun u => u * x * u⁻¹).Nodup) (C : Finset G)
    (hC : ∀ y ∈ C, y ∈ S ∧ y * x = x * y) :
    ∃ d, d ∣ 729 ∧ C.card ≤ d ∧ d * us.length ≤ 729 := by
  classical
  have hfin : Finite S := Nat.finite_of_card_ne_zero (by rw [hS]; norm_num)
  set x' : S := ⟨x, hx⟩
  set K : Subgroup S := Subgroup.centralizer {x'}
  refine ⟨Nat.card K, ?_, ?_, ?_⟩
  · rw [← hS]
    exact Subgroup.card_subgroup_dvd_card K
  ·
    have hmem : ∀ y : C, (⟨(y : G), (hC y y.2).1⟩ : S) ∈ K := by
      intro y
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, x']
      exact (hC y y.2).2
    have hinj : Function.Injective fun y : C => (⟨⟨(y : G), (hC y y.2).1⟩, hmem y⟩ : K) := by
      intro a b hab
      have := congrArg (fun z : K => ((z : S) : G)) hab
      exact Subtype.ext this
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_finsetCard] at this
  ·
    have hcard := Subgroup.card_mul_index K
    rw [hS] at hcard
    rw [← hcard]
    refine Nat.mul_le_mul_left _ ?_
    let f : G → S ⧸ K := fun u => if h : u ∈ S then QuotientGroup.mk (⟨u, h⟩ : S) else
      QuotientGroup.mk 1
    have hconj : ∀ u ∈ us, ∀ v ∈ us, f u = f v → u * x * u⁻¹ = v * x * v⁻¹ := by
      intro u hu v hv h
      simp only [f, dif_pos (hus u hu), dif_pos (hus v hv)] at h
      rw [QuotientGroup.eq, Subgroup.mem_centralizer_singleton_iff] at h
      have h' := congrArg Subtype.val h
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, x'] at h'
      calc u * x * u⁻¹ = u * (x * (u⁻¹ * v)) * v⁻¹ := by group
        _ = u * (u⁻¹ * v * x) * v⁻¹ := by rw [h']
        _ = v * x * v⁻¹ := by group
    have hnd : us.Nodup := List.Nodup.of_map _ hd
    have hf : (us.map f).Nodup := by
      refine List.Nodup.map_on (fun u hu v hv h => ?_) hnd
      exact List.inj_on_of_nodup_map hd hu hv (hconj u hu v hv h)
    have hfin' : Finite (S ⧸ K) := inferInstance
    have := Fintype.ofFinite (S ⧸ K)
    have hl := hf.length_le_card
    rw [List.length_map] at hl
    rw [Subgroup.index, Nat.card_eq_fintype_card]
    exact hl

end CFSG.KC.F4NA

end
