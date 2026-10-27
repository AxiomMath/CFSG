module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVIIProof.CoverHyp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVIIProof.CentEquiv
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Generic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongr

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] [Finite G]

theorem tableVII_isSimple (h28 : Segev28) {a c t t₁ : G} (htc : t ∈ Gxy a c)
    (ht2 : orderOf t = 2) (hY : IsNonsplitDoubleCoverOfS5 ↥(Gxyz a t c)) (ht₁ : t₁ ∈ Gxyz a t c)
    (ht₁2 : t₁ ^ 2 = 1) (ht₁t : t₁ ≠ t) (hk : ∃ k ∈ Gxy a c, k * t * k⁻¹ = t₁) :
    IsSimpleGroup ↥(Gxy a c) := by
  let H := ↥(Gxy a c)
  let t' : H := ⟨t, htc⟩
  have ht2' : orderOf t' = 2 := by
    have h : t' = (⟨t, htc⟩ : H) := rfl
    rw [h, Subgroup.orderOf_mk, ht2]
  let Y := ↥(Gx t')
  let w : Y := GxSelf t'
  have ht_ne : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ht2
    omega
  obtain ⟨k, hkG, hk_eq⟩ := hk
  have ht₁ne : t₁ ≠ 1 := by
    intro h1
    have hord : orderOf t₁ = orderOf t := by
      have h := MulEquiv.orderOf_eq (MulAut.conj k) t
      rwa [MulAut.conj_apply, hk_eq] at h
    rw [h1, orderOf_one, ht2] at hord
    omega
  have ht₁_mem := mem_Gxyz.1 ht₁
  have ht₁Gxy : t₁ ∈ Gxy a c := mem_Gxy.2 ⟨ht₁_mem.1, ht₁_mem.2.2⟩
  have ht₁Gx : (⟨t₁, ht₁Gxy⟩ : H) ∈ Gx t' := by
    refine mem_Gx.2 ?_
    apply Subtype.ext
    show t * t₁ = t₁ * t
    exact mem_Gx.1 ht₁_mem.2.1
  obtain ⟨e, _he⟩ := tableVII_cent_equiv htc
  have hY' : IsNonsplitDoubleCoverOfS5 Y := IsNonsplitDoubleCoverOfS5.of_mulEquiv e.symm hY
  have hw : w ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    show (y : H) * t' = t' * (y : H)
    exact (mem_Gx.1 y.2).symm
  have hw1 : w ≠ 1 := by
    intro h1
    have h2 : t' = 1 := by
      have h := congrArg Subtype.val h1
      simpa [w, GxSelf] using h
    exact ht_ne (by simpa [t'] using congrArg Subtype.val h2)
  obtain ⟨π, hC⟩ := tableVII_cover_of_shape hY' hw hw1
  apply h28 H t' ht2'
  · intro S
    exact tableVII_cover_sylow hC S
  · apply tableVII_eq_closure_of_top (Gx t') (fun x => IsConj t' x)
    let x : Y := ⟨⟨t₁, ht₁Gxy⟩, ht₁Gx⟩
    have hxC : x ∈ {y : Y | IsConj t' (y : H)} := by
      refine isConj_iff.2 ⟨(⟨k, hkG⟩ : H), ?_⟩
      apply Subtype.ext
      show k * t * k⁻¹ = t₁
      exact hk_eq
    have hx2 : x ^ 2 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      show t₁ ^ 2 = 1
      exact ht₁2
    have hx1 : x ≠ 1 := by
      intro h1
      apply ht₁ne
      have h := congrArg (fun y : Y => ((y : H) : G)) h1
      simpa [x] using h
    have hxw : x ≠ w := by
      intro h1
      apply ht₁t
      have h := congrArg (fun y : Y => ((y : H) : G)) h1
      simpa [x, w, GxSelf, t'] using h
    have htop : Subgroup.closure {y : Y | IsConj t' (y : H)} = ⊤ := by
      apply tableVII_cover_closure hC {y : Y | IsConj t' (y : H)}
      · intro g y hy
        have hconj : IsConj t' ((g : H) * (y : H) * (g : H)⁻¹) :=
          hy.trans (isConj_iff.2 ⟨(g : H), rfl⟩)
        exact hconj
      · exact hxC
      · exact hx2
      · exact hx1
      · exact hxw
    exact htop
  · intro N hN hne
    exact tableVII_cover_normal hC N hN hne

end CFSG.EvenSporadicStandard.HNRecog.Section3
