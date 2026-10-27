module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G]

private def cosetMap {H L Y : Subgroup G} (hYH : Y ≤ H) :
    Y ⧸ (Y ⊓ L).subgroupOf Y → H ⧸ L.subgroupOf H :=
  Quotient.map' (fun y : Y => (⟨y.1, hYH y.2⟩ : H)) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    have hL : ((a : G)⁻¹ * (b : G)) ∈ L := by
      simpa using (Subgroup.mem_inf.mp ((Subgroup.mem_subgroupOf).mp hab)).2
    rw [Subgroup.mem_subgroupOf]
    simpa using hL)

private lemma cosetMap_injective {H L Y : Subgroup G} (hYH : Y ≤ H) :
    Function.Injective (cosetMap (L := L) hYH) := by
  refine Quotient.ind₂' ?_
  intro a b hab
  have hHmem : ((⟨a.1, hYH a.2⟩ : H)⁻¹ * ⟨b.1, hYH b.2⟩ : H) ∈ L.subgroupOf H := by
    rw [← QuotientGroup.eq]
    simpa [cosetMap] using hab
  rw [QuotientGroup.eq]
  rw [Subgroup.mem_subgroupOf]
  refine ⟨(a⁻¹ * b).2, ?_⟩
  have hL : ((⟨a.1, hYH a.2⟩ : H)⁻¹ * ⟨b.1, hYH b.2⟩ : H).1 ∈ L :=
    (Subgroup.mem_subgroupOf).mp hHmem
  simpa using hL

private lemma card_subgroupOf_inf {Y L : Subgroup G} :
    Nat.card ((Y ⊓ L).subgroupOf Y) = Nat.card (Y ⊓ L : Subgroup G) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

theorem card_le_card_inf_mul_relIndex {H L Y : Subgroup G} (hLH : L ≤ H) (hYH : Y ≤ H) :
    Nat.card Y ≤ Nat.card (Y ⊓ L : Subgroup G) * L.relIndex H := by
  have hLag := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (s := (Y ⊓ L).subgroupOf Y)
  have hcard := card_subgroupOf_inf (Y := Y) (L := L)
  have hinj : Nat.card (Y ⧸ (Y ⊓ L).subgroupOf Y) ≤ Nat.card (H ⧸ L.subgroupOf H) :=
    Nat.card_le_card_of_injective _ (cosetMap_injective (L := L) hYH)
  calc
    Nat.card Y = Nat.card (Y ⧸ (Y ⊓ L).subgroupOf Y) *
        Nat.card ((Y ⊓ L).subgroupOf Y) := hLag
    _ = Nat.card (Y ⧸ (Y ⊓ L).subgroupOf Y) * Nat.card (Y ⊓ L : Subgroup G) := by rw [hcard]
    _ ≤ Nat.card (H ⧸ L.subgroupOf H) * Nat.card (Y ⊓ L : Subgroup G) :=
      Nat.mul_le_mul_right _ hinj
    _ = Nat.card (Y ⊓ L : Subgroup G) * L.relIndex H := by
      rw [mul_comm]
      rfl

theorem exists_mem_coset_of_card_eq {H L Y : Subgroup G} (hLH : L ≤ H) (hYH : Y ≤ H)
    (hcard : Nat.card Y = Nat.card (Y ⊓ L : Subgroup G) * L.relIndex H) :
    ∀ g ∈ H, ∃ y ∈ Y, g⁻¹ * y ∈ L := by
  have hLag := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (s := (Y ⊓ L).subgroupOf Y)
  have hcardA := card_subgroupOf_inf (Y := Y) (L := L)
  have hcod : Nat.card (H ⧸ L.subgroupOf H) = L.relIndex H := rfl
  have hdom : Nat.card (Y ⧸ (Y ⊓ L).subgroupOf Y) = Nat.card (H ⧸ L.subgroupOf H) := by
    have hp : 0 < Nat.card (Y ⊓ L : Subgroup G) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hp
    calc
      Nat.card (Y ⧸ (Y ⊓ L).subgroupOf Y) * Nat.card (Y ⊓ L : Subgroup G)
          = Nat.card (Y ⧸ (Y ⊓ L).subgroupOf Y) *
              Nat.card ((Y ⊓ L).subgroupOf Y) := by rw [hcardA]
      _ = Nat.card Y := hLag.symm
      _ = Nat.card (Y ⊓ L : Subgroup G) * L.relIndex H := hcard
      _ = Nat.card (Y ⊓ L : Subgroup G) * Nat.card (H ⧸ L.subgroupOf H) := by rw [hcod]
      _ = Nat.card (H ⧸ L.subgroupOf H) * Nat.card (Y ⊓ L : Subgroup G) := Nat.mul_comm _ _
  have hbij : Function.Bijective (cosetMap (L := L) hYH) :=
    (cosetMap_injective (L := L) hYH).bijective_of_nat_card_le (le_of_eq hdom.symm)
  intro g hg
  let x : H ⧸ L.subgroupOf H := QuotientGroup.mk (⟨g, hg⟩ : H)
  obtain ⟨y, hy⟩ := hbij.2 x
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective (s := (Y ⊓ L).subgroupOf Y) y
  refine ⟨y'.1, y'.2, ?_⟩
  have hmem : ((⟨g, hg⟩ : H)⁻¹ * ⟨y'.1, hYH y'.2⟩ : H) ∈ L.subgroupOf H := by
    rw [← QuotientGroup.eq]
    simpa [x, cosetMap] using hy.symm
  simpa using (Subgroup.mem_subgroupOf).mp hmem

theorem ncard_coset_inter {Y L : Subgroup G} {g : G} (hg : ∃ y ∈ Y, g⁻¹ * y ∈ L) :
    {u : G | u ∈ Y ∧ g⁻¹ * u ∈ L}.ncard = Nat.card (Y ⊓ L : Subgroup G) := by
  obtain ⟨w, hwY, hgwL⟩ := hg
  change {u : G | u ∈ Y ∧ g⁻¹ * u ∈ L}.ncard
      = ((Y ⊓ L : Subgroup G) : Set G).ncard
  refine Set.ncard_congr (fun u _ => w⁻¹ * u) ?_ ?_ ?_
  · intro u hu
    refine ⟨?_, ?_⟩
    · exact Y.mul_mem (Y.inv_mem hwY) hu.1
    · have hwu' : (g⁻¹ * w)⁻¹ * (g⁻¹ * u) = w⁻¹ * u := by
        calc
          (g⁻¹ * w)⁻¹ * (g⁻¹ * u) = (w⁻¹ * g) * (g⁻¹ * u) := by
            rw [mul_inv_rev, inv_inv]
          _ = w⁻¹ * (g * (g⁻¹ * u)) := by rw [mul_assoc]
          _ = w⁻¹ * u := by rw [mul_inv_cancel_left]
      rw [← hwu']
      exact L.mul_mem (L.inv_mem hgwL) hu.2
  · intro a b _ _ hab
    exact mul_left_cancel hab
  · intro b hb
    refine ⟨w * b, ⟨?_, ?_⟩, ?_⟩
    · exact Y.mul_mem hwY hb.1
    · have hgb : g⁻¹ * (w * b) = (g⁻¹ * w) * b := by rw [mul_assoc]
      rw [hgb]
      exact L.mul_mem hgwL hb.2
    · exact inv_mul_cancel_left w b

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
