module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.HData2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Count

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

@[expose] def Kgrp {G : Type} [Group G] (ι : Elem2 6 →* G) (z : G) : Subgroup G :=
  normalizer (ι.range : Set G) ⊓ centralizer ({z} : Set G)

structure Setting25 (G : Type) [Group G] (t z z₁ : G) (ι : Elem2 6 →* G) (zv : V6)
    (R0 F : Subgroup G) : Prop where
  injective_ι : Function.Injective ι
  centralizer_le : centralizer (ι.range : Set G) ≤ ι.range
  z_sq : z ^ 2 = 1
  z_ne_one : z ≠ 1
  ι_tv : coordElt ι tv = t
  coords_z₁ : ∃ v : V6, coordElt ι v = z₁ ∧ lam v = 1 ∧ qm v = 0
  omega : inducedGroup ι = OmegaMinus
  card_omega : Nat.card OmegaMinus = 25920
  hD2 : HData2 G t z z₁ ι zv R0 F

variable {G : Type} [Group G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6} {R0 F : Subgroup G}

private lemma card_subtype_eq_of_finset {P : V6 → Prop} {F : Finset V6}
    (h : ∀ v, P v ↔ v ∈ F) : Nat.card {v : V6 // P v} = F.card := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight h), Nat.card_eq_fintype_card, Fintype.card_coe]

theorem Setting25.of_hData [Finite G] {b : G} {S Eg T T' W0 : Subgroup G}
    (hD : HData G t z b z₁ S Eg T T' W0 ι) (hD2 : HData2 G t z z₁ ι zv R0 F)
    (hΩ : inducedGroup ι = OmegaMinus) (hX : ∀ v, IsConj t (coordElt ι v) ↔ qm v = 1) :
    Setting25 G t z z₁ ι zv R0 F := by
  have hcardX : Nat.card {v : V6 // IsConj t (coordElt ι v)} = 36 := by
    rw [card_subtype_eq_of_finset (P := fun v => IsConj t (coordElt ι v)) (F := X36)
      (fun v => (hX v).trans (by simp [X36]))]
    exact card_X36
  have hc : Nat.card (inducedGroup ι) = 25920 := by
    have h := hD.card_inducedGroup
    rw [hcardX] at h
    omega
  exact { injective_ι := hD.injective_ι
          centralizer_le := hD.centralizer_le
          z_sq := hD.z_sq
          z_ne_one := hD.core.z1_ne_one
          ι_tv := hD.ι_tv
          coords_z₁ := hD.coords_z₁
          omega := hΩ
          card_omega := by rw [← hΩ]; exact hc
          hD2 := hD2 }

theorem Setting25.coord_z (h : Setting25 G t z z₁ ι zv R0 F) : coordElt ι zv = z :=
  h.hD2.coordElt_zv

theorem Setting25.zv_ne_zero (h : Setting25 G t z z₁ ι zv R0 F) : zv ≠ 0 := by
  intro hz
  apply h.z_ne_one
  rw [← h.coord_z, hz, coordElt_zero]

end CFSG.EvenSporadicStandard.HNRecog.Harada
