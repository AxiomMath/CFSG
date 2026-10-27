module

public import CFSG.GH74.QTGen4.Recog.G23.Words
public import Certificates.Data.G23RecogWordsInputs
import Certificates.Kernel.Bounds.Family
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public meta import CFSG.GH74.QTGen4.Recog.G23.Words
public meta import CFSG.Certificates.CosetTablePresented
public import CFSG.Quasithin.Recognition.G23TypeDefs

public section

namespace CFSG.GH74.QTGen4.Recog.G23

open CFSG.CosetTable

open CFSG.Quasithin.G23Type
open scoped MatrixGroups Pointwise

theorem card_sl2_zmod3 : Nat.card SL(2, ZMod 3) = 24 := by
  rw [Matrix.card_SL_field 2]
  simp [ZMod.card, Fin.prod_univ_two]

variable {G : Type*} [Group G]

theorem card_H₁_of_G23One {H H₁ H₂ : Subgroup G} (hH : G23One H H₁ H₂) :
    Nat.card H₁ = 24 := by
  obtain ⟨e⟩ := hH.iso_one
  rw [Nat.card_congr e.toEquiv, card_sl2_zmod3]

theorem card_H₂_of_G23One {H H₁ H₂ : Subgroup G} (hH : G23One H H₁ H₂) :
    Nat.card H₂ = 24 := by
  obtain ⟨e⟩ := hH.iso_two
  rw [Nat.card_congr e.toEquiv, card_sl2_zmod3]

theorem card_sup_mul_two_of_G23One {H H₁ H₂ : Subgroup G} (hH : G23One H H₁ H₂) :
    Nat.card ↥(H₁ ⊔ H₂) * 2 = Nat.card ↥H := by
  have hle : H₁ ⊔ H₂ ≤ H := sup_le hH.le_one hH.le_two
  have h := Subgroup.card_mul_index ((H₁ ⊔ H₂).subgroupOf H)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, ← Subgroup.relIndex,
    hH.index] at h
  exact h

theorem card_sup_eq_mul_card_image {N K : Subgroup G} [N.Normal] :
    Nat.card ↥(N ⊔ K) = Nat.card ↥N * Nat.card ((K : Set G).image (QuotientGroup.mk' N)) := by
  have h1 : Nat.card ((K : Set G) * (N : Set G)) =
      Nat.card ↥N * Nat.card ((K : Set G).image (QuotientGroup.mk' N)) :=
    Subgroup.card_mul_eq_card_subgroup_mul_card_quotient (s := N) (t := (K : Set G))
  have h2 : (K : Set G) * (N : Set G) = ((N ⊔ K : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact (Subgroup.mul_normal K N).symm
  rw [← h1, h2]
  rfl

theorem card_inf_mul_card_image_eq {N K : Subgroup G} [N.Normal] :
    Nat.card ↥(N ⊓ K) * Nat.card ((K : Set G).image (QuotientGroup.mk' N)) = Nat.card ↥K := by
  set f : K →* G ⧸ N := (QuotientGroup.mk' N).comp K.subtype with hf
  have hkerEq : f.ker = (N ⊓ K).subgroupOf K := by
    ext x
    simp [hf, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hset : (K : Set G).image (QuotientGroup.mk' N) = (f.range : Set (G ⧸ N)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨⟨y, hy⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
  have hcard := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hkerEq,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : N ⊓ K ≤ K)).toEquiv] at hcard
  rw [hset]
  exact hcard

theorem card_H_of_G23One {H H₁ H₂ : Subgroup G} (hH : G23One H H₁ H₂) :
    Nat.card ↥H = 576 := by
  have hA : (H₁.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (H := H₁) (K := H) hH.le_one).2 hH.normal_one
  have hB : (H₂.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (H := H₂) (K := H) hH.le_two).2 hH.normal_two
  have hle : H₁ ⊔ H₂ ≤ H := sup_le hH.le_one hH.le_two
  have hsup : H₁.subgroupOf H ⊔ H₂.subgroupOf H = (H₁ ⊔ H₂).subgroupOf H :=
    (Subgroup.subgroupOf_sup hH.le_one hH.le_two).symm
  have hinf : H₁.subgroupOf H ⊓ H₂.subgroupOf H = (H₁ ⊓ H₂).subgroupOf H := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  have hP := card_sup_eq_mul_card_image (G := ↥H) (N := H₁.subgroupOf H) (K := H₂.subgroupOf H)
  have hQ := card_inf_mul_card_image_eq (G := ↥H) (N := H₁.subgroupOf H) (K := H₂.subgroupOf H)
  have hcA : Nat.card ↥(H₁.subgroupOf H) = 24 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH.le_one).toEquiv, card_H₁_of_G23One hH]
  have hcB : Nat.card ↥(H₂.subgroupOf H) = 24 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH.le_two).toEquiv, card_H₂_of_G23One hH]
  have hcI : Nat.card ↥(H₁.subgroupOf H ⊓ H₂.subgroupOf H) = 2 := by
    rw [hinf, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hH.le_one)).toEquiv,
      hH.card_inf]
  have hS : Nat.card ↥(H₁.subgroupOf H ⊔ H₂.subgroupOf H) = Nat.card ↥(H₁ ⊔ H₂) := by
    rw [hsup]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hmul := card_sup_mul_two_of_G23One hH
  rw [hcA] at hP
  rw [hcI, hcB] at hQ
  rw [hS] at hP
  omega

end CFSG.GH74.QTGen4.Recog.G23
