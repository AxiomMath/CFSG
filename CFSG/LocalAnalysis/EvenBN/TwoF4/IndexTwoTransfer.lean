module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.FusionControl

public section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup

variable {G : Type*} [Group G]

open Classical in
@[expose] noncomputable def indexTwoSign (X Y : Subgroup G) (hY : Y.relIndex X = 2) : X →* ℤˣ where
  toFun x := if (x : G) ∈ Y then 1 else -1
  map_one' := by simp
  map_mul' a b := by
    have hmul := Subgroup.mul_mem_iff_of_index_two (H := Y.subgroupOf X) hY (a := a) (b := b)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at hmul
    by_cases ha : (a : G) ∈ Y <;> by_cases hb : (b : G) ∈ Y <;> simp [ha, hb, hmul]

theorem indexTwoSign_apply_of_mem {X Y : Subgroup G} (hY : Y.relIndex X = 2) {x : X}
    (hx : (x : G) ∈ Y) : indexTwoSign X Y hY x = 1 := by
  classical
  change (if (x : G) ∈ Y then (1 : ℤˣ) else -1) = 1
  simp [hx]

theorem indexTwoSign_apply_of_not_mem {X Y : Subgroup G} (hY : Y.relIndex X = 2) {x : X}
    (hx : (x : G) ∉ Y) : indexTwoSign X Y hY x = -1 := by
  classical
  change (if (x : G) ∈ Y then (1 : ℤˣ) else -1) = -1
  simp [hx]

theorem indexTwoSign_eq_neg_one_iff {X Y : Subgroup G} (hY : Y.relIndex X = 2) (x : X) :
    indexTwoSign X Y hY x = -1 ↔ (x : G) ∉ Y := by
  by_cases hx : (x : G) ∈ Y
  · rw [indexTwoSign_apply_of_mem hY hx]
    exact ⟨fun h => absurd h (by decide), fun h => absurd hx h⟩
  · rw [indexTwoSign_apply_of_not_mem hY hx]
    exact ⟨fun _ => hx, fun _ => rfl⟩

variable [Finite G]

theorem false_of_index_two_coset_conj_of_hom_eq_one (hG : ∀ ψ : G →* ℤˣ, ψ = 1) {t : G}
    (ht : t * t = 1) {X Y : Subgroup G} (hidx : Y.relIndex X = 2) (htX : t ∈ X) (htY : t ∉ Y)
    (hfus : ∀ g : G, g⁻¹ * t * g ∈ X → g⁻¹ * t * g ∉ Y → ∃ x ∈ X, g⁻¹ * t * g = x⁻¹ * t * x)
    (hsyl : ¬ 2 ∣ X.relIndex (centralizer ({t} : Set G))) : False := by
  refine CFSG.EvenSporadicStandard.false_of_fusion_control hG ht X htX (indexTwoSign X Y hidx)
    (indexTwoSign_apply_of_not_mem hidx htY) ?_ hsyl
  rintro y hy ⟨g, hg⟩
  have hgy : g⁻¹⁻¹ * t * g⁻¹ = y := by rw [inv_inv, hg]
  obtain ⟨x, hx, hxy⟩ := hfus g⁻¹ (hgy ▸ y.2)
    (hgy ▸ (indexTwoSign_eq_neg_one_iff hidx y).1 hy)
  refine ⟨x⁻¹, X.inv_mem hx, ?_⟩
  rw [inv_inv, ← hxy, hgy]

theorem false_of_index_two_coset_conj [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {t : G} (ht : orderOf t = 2) {X Y : Subgroup G} (hidx : Y.relIndex X = 2) (htX : t ∈ X)
    (htY : t ∉ Y)
    (hfus : ∀ g : G, g⁻¹ * t * g ∈ X → g⁻¹ * t * g ∉ Y → ∃ x ∈ X, g⁻¹ * t * g = x⁻¹ * t * x)
    (hsyl : ¬ 2 ∣ X.relIndex (centralizer ({t} : Set G))) : False :=
  false_of_index_two_coset_conj_of_hom_eq_one
    (CFSG.EvenSporadicStandard.hom_units_eq_one_of_simple hnonab)
    (by rw [← pow_two, ← ht, pow_orderOf_eq_one]) hidx htX htY hfus hsyl

end CFSG.LocalAnalysis.EvenBN.TwoF4
