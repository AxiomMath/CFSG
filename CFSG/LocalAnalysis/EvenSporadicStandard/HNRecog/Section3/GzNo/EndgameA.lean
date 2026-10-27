module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Special
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Count
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Qz
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Symm

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem gzNo_exists_z1 {G : Type} [Group G] [Finite G] {z x y : G} (hx : GzNoSpecial z x)
    (hy : GzNoSpecial z y) (hDy : Qz z ⊓ Gx x ≤ Gx y) :
    ∃ z₁ : G, z₁ ∈ Qz z ⊓ Qz x ∧ z₁ ∈ Qz y ∧ z₁ ≠ 1 := by
  have hD : Qz z ⊓ Gx x = Qz z ⊓ Gx y :=
    Subgroup.eq_of_le_of_card_ge (le_inf inf_le_left hDy)
      (by rw [hx.card_cent, hy.card_cent])
  have hSx : Qz z ⊓ Qz x ≤ Qz z ⊓ Gx x := inf_le_inf_left _ (gzNo_Qz_le x)
  have hSy : Qz z ⊓ Qz y ≤ Qz z ⊓ Gx x := by
    rw [hD]
    exact inf_le_inf_left _ (gzNo_Qz_le y)
  have h1 := gzNo_card_mul_le hSx hSy
  rw [hx.card_inter, hy.card_inter, hx.card_cent] at h1
  have h2 : 1 < Nat.card ↥((Qz z ⊓ Qz x) ⊓ (Qz z ⊓ Qz y)) := by
    have h3 : (2 : ℕ) ^ 4 * 2 ^ 4 = 256 := by norm_num
    have h4 : (2 : ℕ) ^ 5 = 32 := by norm_num
    rw [h3, h4] at h1
    omega
  obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    ((Subgroup.one_lt_card_iff_ne_bot _).mp h2)
  have hw' := Subgroup.mem_inf.mp w.2
  exact ⟨w, hw'.1, (Subgroup.mem_inf.mp hw'.2).2, fun h => hw (Subtype.ext h)⟩

theorem gzNo_inter_le_Qz {G : Type} [Group G] [Finite G] {a z : G} (h : IsF5Type a z)
    (hOrb : Vert GzOrbitFacts a z) {x z₁ : G} (hx : GzNoSpecial z x)
    (hxz₁ : GzNoSpecial z (x * z₁)) (hz₁ : z₁ ∈ Qz z ⊓ Qz x) (hz₁1 : z₁ ≠ 1) :
    (Qz z ⊓ Qz x) ⊓ (Qz z ⊓ Qz (x * z₁)) ≤ Qz z₁ := by
  intro t ht
  by_cases ht1 : t = 1
  · rw [ht1]
    exact Subgroup.one_mem _
  have htx : t ∈ Qz z ⊓ Qz x := (Subgroup.mem_inf.mp ht).1
  have htxz : t ∈ Qz z ⊓ Qz (x * z₁) := (Subgroup.mem_inf.mp ht).2
  have htB : IsConj z t := hx.twoB_inter t htx ht1
  have h1 : x ∈ Qz t := gzNo_mem_Qz_symm h hOrb hx.twoB htB (Subgroup.mem_inf.mp htx).2
  have h2 : x * z₁ ∈ Qz t :=
    gzNo_mem_Qz_symm h hOrb hxz₁.twoB htB (Subgroup.mem_inf.mp htxz).2
  have h3 : z₁ ∈ Qz t := by
    have h4 := mul_mem (inv_mem h1) h2
    rwa [inv_mul_cancel_left] at h4
  exact gzNo_mem_Qz_symm h hOrb htB (hx.twoB_inter z₁ hz₁ hz₁1) h3

end CFSG.EvenSporadicStandard.HNRecog.Section3
