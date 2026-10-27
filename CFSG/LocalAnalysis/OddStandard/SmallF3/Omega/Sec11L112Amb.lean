module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L114
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109A2Card
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109BCard

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11_cenSA [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) {c : G} (hc : c ∈ S)
    (hcA : ∀ a ∈ secA t S L, c * a = a * c) : c ∈ secA t S L := by
  obtain ⟨hpsp, -, -, -, hSN, hsyl⟩ := hp.basic G t L S z hctx.toSec10Z
  have hBA : secB S L ≤ secA t S L := le_sup_left
  have hmem : c ∈ JElem (S ⊓ L) ⊔ centralizer (L : Set G) :=
    hp.facts.centB5 G L hpsp (S ⊓ L) hsyl c (hSN hc) fun b hb => hcA b (hBA hb)
  have hcomm : ∀ b ∈ JElem (S ⊓ L), ∀ y ∈ centralizer (L : Set G), b * y = y * b := by
    intro b hb y hy
    exact Subgroup.mem_centralizer_iff.mp hy b (secB_le_L S L hb)
  obtain ⟨b, hb, y, hy, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hmem
  have hyS : y ∈ S := by
    have h1 : b⁻¹ * (b * y) ∈ S := S.mul_mem (S.inv_mem (secB_le_S S L hb)) hc
    simpa using h1
  have hyt : y ∈ zpowers t := by
    rw [← hp.r10.l106 G t L S z K1 K2 hctx]
    exact ⟨hy, hyS⟩
  exact (secA t S L).mul_mem (hBA hb) (mem_sup_right hyt)

theorem sec11_cenTA [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) {c : G} (hc : c ∈ T)
    (hcA : ∀ a ∈ secA t S L, c * a = a * c) : c ∈ secA t S L := by
  obtain ⟨-, -, -, -, htS, -⟩ := hp.basic G t L S z hctx.toSec10Z
  have htA : t ∈ secA t S L := mem_sup_right (mem_zpowers t)
  have hcS : c ∈ S :=
    sec11L114_cent_le hctx.sylow hctx.sylowT.2.1 hctx.S_le hc (hcA t htA)
  exact sec11_cenSA hp hctx.toSec10Ctx hcS hcA

theorem sec11_A_inf_L [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) {x : G} (hxA : x ∈ secA t S L)
    (hxL : x ∈ L) : x ∈ secB S L := by
  obtain ⟨-, -, htL, -, -, -⟩ := hp.basic G t L S z hctx.toSec10Z
  have hBt : secB S L ⊔ zpowers t = secA t S L := rfl
  have hcomm : ∀ b ∈ secB S L, ∀ y ∈ zpowers t, b * y = y * b := by
    intro b hb y hy
    obtain ⟨-, htc, -, -, -, -⟩ := hp.basic G t L S z hctx.toSec10Z
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hbt : b * t = t * b := Subgroup.mem_centralizer_iff.mp htc b (secB_le_L S L hb)
    exact ((Commute.zpow_right (show Commute b t from hbt) k).eq)
  obtain ⟨b, hb, y, hy, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hxA
  have hyL : y ∈ L := by
    have h1 : b⁻¹ * (b * y) ∈ L := L.mul_mem (L.inv_mem (secB_le_L S L hb)) hxL
    simpa using h1
  have hy1 : y ∈ secB S L := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have ht2 : t * t = 1 := by
      have h2 : orderOf t = 2 := hctx.involution
      rw [← pow_two, ← h2]
      exact pow_orderOf_eq_one t
    have hk : t ^ k = 1 ∨ t ^ k = t := by
      have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht2]
      have hk' : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
      rw [hk', zpow_add, zpow_mul, h2, one_zpow, one_mul]
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · left
        rw [h, zpow_zero]
      · right
        rw [h, zpow_one]
    rcases hk with h | h
    · rw [h]
      exact (secB S L).one_mem
    · exact absurd (h ▸ hyL) htL
  exact (secB S L).mul_mem hb hy1

theorem sec11_Q_mul_mem [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) {a b : G} (ha : a ∈ S ⊓ L)
    (hb : b ∈ S ⊓ L) (haQ : a ∉ secQ K1 K2) (hbQ : b ∉ secQ K1 K2) : a * b ∈ secQ K1 K2 := by
  have hpsp : IsPSp43 L := (hp.basic G t L S z hctx.toSec10Z).1
  have hQP : secQ K1 K2 ≤ S ⊓ L := sec10J_Q_le hp.facts.pockets5 hp.basic hctx
  have hP64 : Nat.card ↥(S ⊓ L) = 64 := sec10A2_card_P hp.facts hp.basic hctx
  have hQ32 : 32 ≤ Nat.card ↥(secQ K1 K2) :=
    sec10B_card_Q hp.facts.pockets5 hp.facts.centZ5 hpsp hctx
  have h1 := Subgroup.relIndex_mul_card (H := secQ K1 K2) (K := S ⊓ L)
  rw [inf_of_le_left hQP, hP64] at h1
  have hidx : (secQ K1 K2).relIndex (S ⊓ L) = 1 ∨ (secQ K1 K2).relIndex (S ⊓ L) = 2 := by
    have hle : (secQ K1 K2).relIndex (S ⊓ L) ≤ 2 := by
      by_contra hgt
      have h3 : 3 * 32 ≤ (secQ K1 K2).relIndex (S ⊓ L) * Nat.card ↥(secQ K1 K2) :=
        Nat.mul_le_mul (by omega) hQ32
      omega
    have hpos : 0 < (secQ K1 K2).relIndex (S ⊓ L) := by
      rcases Nat.eq_zero_or_pos ((secQ K1 K2).relIndex (S ⊓ L)) with h | h
      · rw [h] at h1
        omega
      · exact h
    omega
  rcases hidx with h | h
  · exact absurd (Subgroup.relIndex_eq_one.mp h ha) haQ
  · have hind : ((secQ K1 K2).subgroupOf (S ⊓ L)).index = 2 := h
    have key := Subgroup.mul_mem_iff_of_index_two hind (a := (⟨a, ha⟩ : ↥(S ⊓ L)))
      (b := (⟨b, hb⟩ : ↥(S ⊓ L)))
    have hnot : ¬ ((⟨a, ha⟩ : ↥(S ⊓ L)) ∈ (secQ K1 K2).subgroupOf (S ⊓ L)) := haQ
    have hnot' : ¬ ((⟨b, hb⟩ : ↥(S ⊓ L)) ∈ (secQ K1 K2).subgroupOf (S ⊓ L)) := hbQ
    exact key.mpr (iff_of_false hnot hnot')

end CFSG.OddStandard.SmallF3.Omega
