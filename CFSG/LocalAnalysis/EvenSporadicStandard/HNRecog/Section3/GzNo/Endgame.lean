module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Special
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.XFusion
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Count
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Adjoin
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Qz
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.QzRank
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Symm
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.EndgameA
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Transport

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem gzNo_endgame (hC : CSideFacts) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hOrb : Vert GzOrbitFacts a z) {x y z₁ : G} (hxz : x ∈ Gx z)
    (hyz : y ∈ Gx z) (hx : GzNoSpecial z x) (hy : GzNoSpecial z y)
    (hxz₁ : GzNoSpecial z (x * z₁)) (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1) (hyx : y * x = x * y)
    (hxyQ : x * y ∉ Qz z) (hDy : Qz z ⊓ Gx x ≤ Gx y) (hz₁ : z₁ ∈ Qz z ⊓ Qz x)
    (hz₁y : z₁ ∈ Qz y) (hz₁1 : z₁ ≠ 1) : False := by
  have hz2 : z ^ 2 = 1 := by
    rw [← h.orderOf_z]
    exact pow_orderOf_eq_one z
  have hz₁Q : z₁ ∈ Qz z := (Subgroup.mem_inf.mp hz₁).1
  have hz₁x : z₁ ∈ Qz x := (Subgroup.mem_inf.mp hz₁).2
  have hz₁B : IsConj z z₁ := hx.twoB_inter z₁ hz₁ hz₁1
  have hDle : Qz z ⊓ Gx x ≤ Qz z ⊓ Gx (x * z₁) := by
    intro d hd
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hd).1, ?_⟩
    rw [mem_Gx]
    have hdx : x * d = d * x := mem_Gx.mp (Subgroup.mem_inf.mp hd).2
    have hdz : d * z₁ = z₁ * d := gzNo_commute_of_mem_inf h hd hz₁ hx.z_not_mem
    calc (x * z₁) * d = x * (z₁ * d) := by group
      _ = x * (d * z₁) := by rw [← hdz]
      _ = (x * d) * z₁ := by group
      _ = (d * x) * z₁ := by rw [hdx]
      _ = d * (x * z₁) := by group
  have hDeq : Qz z ⊓ Gx x = Qz z ⊓ Gx (x * z₁) := by
    refine Subgroup.eq_of_le_of_card_ge hDle ?_
    rw [hx.card_cent, hxz₁.card_cent]
  have hSle : Qz z ⊓ Qz x ≤ Qz z ⊓ Gx x := by
    intro d hd
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_inf.mp hd).1, gzNo_Qz_le x (Subgroup.mem_inf.mp hd).2⟩
  have hS'le : Qz z ⊓ Qz (x * z₁) ≤ Qz z ⊓ Gx x := by
    rw [hDeq]
    intro d hd
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_inf.mp hd).1, gzNo_Qz_le (x * z₁) (Subgroup.mem_inf.mp hd).2⟩
  have hcount := gzNo_card_mul_le (K := G)
    (H := Qz z ⊓ Qz x) (L := Qz z ⊓ Qz (x * z₁)) (D := Qz z ⊓ Gx x) hSle hS'le
  have hT8 : 8 ≤ Nat.card ↥((Qz z ⊓ Qz x) ⊓ (Qz z ⊓ Qz (x * z₁))) := by
    rw [hx.card_inter, hxz₁.card_inter, hx.card_cent] at hcount
    norm_num at hcount
    have h8 : 8 * 32 ≤ Nat.card ↥((Qz z ⊓ Qz x) ⊓ (Qz z ⊓ Qz (x * z₁))) * 32 := by
      calc 8 * 32 = 256 := by norm_num
        _ ≤ 32 * Nat.card ↥((Qz z ⊓ Qz x) ⊓ (Qz z ⊓ Qz (x * z₁))) := hcount
        _ = Nat.card ↥((Qz z ⊓ Qz x) ⊓ (Qz z ⊓ Qz (x * z₁))) * 32 := by ring
    exact le_of_mul_le_mul_right h8 (by norm_num)
  have hTM : ((Qz z ⊓ Qz x) ⊓ (Qz z ⊓ Qz (x * z₁))) ≤ Qz z₁ :=
    gzNo_inter_le_Qz h hOrb hx hxz₁ hz₁ hz₁1
  have hzQz₁ : z ∈ Qz z₁ := gzNo_mem_Qz_symm h hOrb (IsConj.refl z) hz₁B hz₁Q
  have hxQz₁ : x ∈ Qz z₁ := gzNo_mem_Qz_symm h hOrb hx.twoB hz₁B hz₁x
  have hyQz₁ : y ∈ Qz z₁ := gzNo_mem_Qz_symm h hOrb hy.twoB hz₁B hz₁y
  have hT2 : ∀ t ∈ ((Qz z ⊓ Qz x) ⊓ (Qz z ⊓ Qz (x * z₁))), t ^ 2 = 1 := by
    intro t ht
    exact hx.sq_inter t (Subgroup.mem_inf.mp ht).1
  have hTN : ((Qz z ⊓ Qz x) ⊓ (Qz z ⊓ Qz (x * z₁))) ≤ Qz z := by
    intro t ht
    exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ht).1).1
  have hzN : z ∈ Qz z := self_mem_Qz hz2
  have hzT : z ∉ ((Qz z ⊓ Qz x) ⊓ (Qz z ⊓ Qz (x * z₁))) := by
    intro ht
    exact hx.z_not_mem (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ht).1).2
  have hzx : z * x = x * z := mem_Gx.mp hxz
  have hzy : z * y = y * z := mem_Gx.mp hyz
  have hxy : x * y = y * x := hyx.symm
  have hTz : ∀ t ∈ ((Qz z ⊓ Qz x) ⊓ (Qz z ⊓ Qz (x * z₁))), t * z = z * t := by
    intro t ht
    exact (mem_Gx.mp (gzNo_Qz_le z (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ht).1).1)).symm
  have hTx : ∀ t ∈ ((Qz z ⊓ Qz x) ⊓ (Qz z ⊓ Qz (x * z₁))), t * x = x * t := by
    intro t ht
    exact (mem_Gx.mp (gzNo_Qz_le x (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ht).1).2)).symm
  have hTD : ((Qz z ⊓ Qz x) ⊓ (Qz z ⊓ Qz (x * z₁))) ≤ Qz z ⊓ Gx x := by
    intro t ht
    exact hSle (Subgroup.mem_inf.mp ht).1
  have hTy : ∀ t ∈ ((Qz z ⊓ Qz x) ⊓ (Qz z ⊓ Qz (x * z₁))), t * y = y * t := by
    intro t ht
    exact (mem_Gx.mp (hDy (hTD ht))).symm
  obtain ⟨E, hEM, hEl, hEcard⟩ :=
    gzNo_exists_elem_sixtyfour (M := Qz z₁) (N := Qz z)
      (T := (Qz z ⊓ Qz x) ⊓ (Qz z ⊓ Qz (x * z₁)))
      hT2 hT8 hTM hTN hzQz₁ hxQz₁ hyQz₁ hz2 hx2 hy2 hzN hzT hx.not_mem hy.not_mem hxyQ
      hzx hzy hxy hTz hTx hTy
  have hle5 : Nat.card E ≤ 2 ^ 5 :=
    gzNo_card_le_of_le_Qz hC (isF5Type_of_isConj h (IsConj.refl a) hz₁B) hEM hEl
  norm_num at hEcard hle5
  omega

end CFSG.EvenSporadicStandard.HNRecog.Section3
