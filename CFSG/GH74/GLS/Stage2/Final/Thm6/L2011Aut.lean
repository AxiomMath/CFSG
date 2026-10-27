module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_14Pair
public import CFSG.GH74.GLS.Stage2.Final.Thm6.SL2BoundBar
public import CFSG.GH74.GLS.Stage2.Local.P34Bar

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L20 CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage2.Local.P34

section Act

@[expose] def quotAct {Actor Value : Type*} [Monoid Actor] [Group Value] (action : Actor →* MulAut Value)
    (N : Subgroup Value) [hN : N.Characteristic] : Actor →* MulAut (Value ⧸ N) where
  toFun a := QuotientGroup.congr N N (action a) (by
    rw [← MulEquiv.toMonoidHom_eq_coe]
    exact Subgroup.characteristic_iff_map_eq.mp hN (action a))
  map_one' := by
    ext element
    obtain ⟨preimage, rfl⟩ := QuotientGroup.mk'_surjective N element
    simp only [QuotientGroup.congr_mk', map_one, MulAut.one_apply]
  map_mul' := by
    intro first second
    ext element
    obtain ⟨preimage, rfl⟩ := QuotientGroup.mk'_surjective N element
    simp only [MulAut.mul_apply]
    rw [QuotientGroup.congr_mk', QuotientGroup.congr_mk', QuotientGroup.congr_mk', map_mul]
    rfl

theorem quotAct_mk {Actor Value : Type*} [Monoid Actor] [Group Value] (action : Actor →* MulAut Value)
    (N : Subgroup Value) [N.Characteristic] (a : Actor) (v : Value) :
    quotAct action N a (v : Value ⧸ N) = ((action a v : Value) : Value ⧸ N) := rfl

variable {G : Type} [Group G]

theorem normal_subgroupOf_of_conj {H J : Subgroup G} (hJH : J ≤ H)
    (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) : (J.subgroupOf H).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hJH]
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro m
  constructor
  · exact fun hm => hJn h hh m hm
  · intro hm
    have := hJn h⁻¹ (H.inv_mem hh) _ hm
    have e : h⁻¹ * (h * m * h⁻¹) * h⁻¹⁻¹ = m := by group
    rwa [e] at this

end Act

section Act2

variable {G : Type} [Group G] {H J : Subgroup G}

@[expose] def cjHom (hJH : J ≤ H) (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) : ↥H →* MulAut ↥J :=
  haveI := normal_subgroupOf_of_conj hJH hJn
  (MulAut.congr (Subgroup.subgroupOfEquivOfLe hJH)).toMonoidHom.comp
    (MulAut.conjNormal (H := J.subgroupOf H))

@[expose] def actB (hJH : J ≤ H) (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) : ↥H →* MulAut (HBar J) :=
  quotAct (cjHom hJH hJn) (pPrimeCore 2 ↥J)

theorem actB_mk (hJH : J ≤ H) (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) (h : ↥H) (j : ↥J) :
    actB hJH hJn h (mkH J j) = mkH J ⟨(h : G) * (j : G) * (h : G)⁻¹, hJn h h.2 j j.2⟩ := by
  unfold actB
  rw [show mkH J j = ((j : ↥J) : HBar J) from rfl, quotAct_mk]
  rfl

end Act2

section Act3

variable {G : Type} [Group G] {H J : Subgroup G}

theorem actB_inner (hJH : J ≤ H) (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) (j : ↥J) :
    actB hJH hJn ⟨(j : G), hJH j.2⟩ = MulAut.conj (mkH J j) := by
  ext k
  obtain ⟨j', rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥J) k
  have h1 := actB_mk hJH hJn ⟨(j : G), hJH j.2⟩ j'
  have e : (⟨(j : G) * (j' : G) * (j : G)⁻¹, hJn (j : G) (hJH j.2) j' j'.2⟩ : ↥J) = j * j' * j⁻¹ := rfl
  rw [MulAut.conj_apply]
  change actB hJH hJn ⟨(j : G), hJH j.2⟩ (mkH J j') = _
  rw [h1]
  show mkH J _ = mkH J j * mkH J j' * (mkH J j)⁻¹
  rw [e, map_mul, map_mul, map_inv]

theorem conj_mem_range_actB (hJH : J ≤ H) (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) (k : HBar J) :
    MulAut.conj k ∈ (actB hJH hJn).range := by
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥J) k
  exact ⟨⟨(j : G), hJH j.2⟩, actB_inner hJH hJn j⟩

theorem actB_core (hJH : J ≤ H) (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) (p : ↥J)
    (hp : p ∈ pPrimeCore 2 ↥J) : actB hJH hJn ⟨(p : G), hJH p.2⟩ = 1 := by
  have h1 := actB_inner hJH hJn p
  have h2 : mkH J p = 1 := (mkH_eq_one_iff J).2 hp
  rw [h1, h2]
  ext k
  simp

theorem actB_fix (hJH : J ≤ H) (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) {z : G} (hz : z ∈ J) {f : G}
    (hf : f ∈ H) (hfz : f * z = z * f) :
    actB hJH hJn ⟨f, hf⟩ (mkH J ⟨z, hz⟩) = mkH J ⟨z, hz⟩ := by
  rw [actB_mk]
  congr 1
  apply Subtype.ext
  show f * z * f⁻¹ = z
  rw [hfz]; group

theorem exists_cen_actB_eq [Finite G] (hJH : J ≤ H) (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) {z : G} (hz : z ∈ J)
    (hz2 : orderOf z = 2) (h : ↥H) (hfix : actB hJH hJn h (mkH J ⟨z, hz⟩) = mkH J ⟨z, hz⟩) :
    ∃ c : ↥H, (c : G) ∈ Cen z ∧ actB hJH hJn c = actB hJH hJn h := by
  have hzJ : orderOf (⟨z, hz⟩ : ↥J) = 2 := by
    rw [← hz2]; exact (Subgroup.orderOf_coe (⟨z, hz⟩ : ↥J)).symm
  have hu : (⟨(h : G) * z * (h : G)⁻¹, hJn h h.2 z hz⟩ : ↥J) = ⟨(h : G) * z * (h : G)⁻¹, hJn h h.2 z hz⟩ := rfl
  have huord : orderOf (⟨(h : G) * z * (h : G)⁻¹, hJn h h.2 z hz⟩ : ↥J) = 2 := by
    rw [← Subgroup.orderOf_coe]
    have h1 := MulEquiv.orderOf_eq (MulAut.conj (h : G)) z
    rw [MulAut.conj_apply] at h1
    rw [show ((⟨(h : G) * z * (h : G)⁻¹, hJn h h.2 z hz⟩ : ↥J) : G) = (h : G) * z * (h : G)⁻¹ from rfl, h1, hz2]
  have hmk : mkH J ⟨(h : G) * z * (h : G)⁻¹, hJn h h.2 z hz⟩ = mkH J ⟨z, hz⟩ := by
    rw [← actB_mk hJH hJn h ⟨z, hz⟩]; exact hfix
  obtain ⟨p, hpO, hpe⟩ := exists_mem_core_conj J hzJ huord hmk
  refine ⟨⟨(p : G) * (h : G), H.mul_mem (hJH p.2) h.2⟩, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : (h : G) * z * (h : G)⁻¹ = (p : G)⁻¹ * z * (p : G) := congrArg Subtype.val hpe
    show (p : G) * (h : G) * z = z * ((p : G) * (h : G))
    have : (p : G) * ((h : G) * z * (h : G)⁻¹) * (p : G)⁻¹ = z := by
      rw [h1]; group
    calc (p : G) * (h : G) * z = ((p : G) * ((h : G) * z * (h : G)⁻¹) * (p : G)⁻¹) * ((p : G) * (h : G)) := by group
      _ = z * ((p : G) * (h : G)) := by rw [this]
  · have h1 : (⟨(p : G) * (h : G), H.mul_mem (hJH p.2) h.2⟩ : ↥H) = ⟨(p : G), hJH p.2⟩ * h := rfl
    rw [h1, map_mul, actB_core hJH hJn p hpO, one_mul]

end Act3

section Yimg

variable {G : Type} [Group G] {H J : Subgroup G}

@[expose] def Yimg (hJH : J ≤ H) (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) (F₂ : Subgroup G) :
    Subgroup (MulAut (HBar J)) :=
  (F₂.subgroupOf H).map (actB hJH hJn)

theorem Yimg_le_range (hJH : J ≤ H) (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) (F₂ : Subgroup G) :
    Yimg hJH hJn F₂ ≤ (actB hJH hJn).range := Subgroup.map_le_range _ _

theorem Yimg_fix (hJH : J ≤ H) (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) {z : G} (hz : z ∈ J)
    {F₂ : Subgroup G} (hF₂z : ∀ f ∈ F₂, f * z = z * f) :
    ∀ β ∈ Yimg hJH hJn F₂, β (mkH J ⟨z, hz⟩) = mkH J ⟨z, hz⟩ := by
  rintro β ⟨f', hf', rfl⟩
  exact actB_fix hJH hJn hz f'.2 (hF₂z _ (Subgroup.mem_subgroupOf.1 hf'))

theorem Yimg_norm [Finite G] (hJH : J ≤ H) (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) {z : G} (hz : z ∈ J)
    (hz2 : orderOf z = 2) {F₂ : Subgroup G}
    (hnorm : ∀ c ∈ Cen z, c ∈ H → ∀ f ∈ F₂, c * f * c⁻¹ ∈ F₂) :
    ∀ γ ∈ (actB hJH hJn).range, γ (mkH J ⟨z, hz⟩) = mkH J ⟨z, hz⟩ →
      ∀ β ∈ Yimg hJH hJn F₂, γ * β * γ⁻¹ ∈ Yimg hJH hJn F₂ := by
  rintro γ ⟨h, rfl⟩ hγ β ⟨f', hf', rfl⟩
  obtain ⟨c, hcC, hc⟩ := exists_cen_actB_eq hJH hJn hz hz2 h hγ
  rw [← hc]
  refine ⟨c * f' * c⁻¹, ?_, by simp⟩
  show c * f' * c⁻¹ ∈ F₂.subgroupOf H
  rw [Subgroup.mem_subgroupOf]
  exact hnorm c hcC c.2 f' (Subgroup.mem_subgroupOf.1 hf')

theorem Yimg_odd (hJH : J ≤ H) (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) {F₂ : Subgroup G}
    (hF₂H : F₂ ≤ H) (hodd : Odd (Nat.card ↥F₂)) : Odd (Nat.card ↥(Yimg hJH hJn F₂)) := by
  have h1 : Nat.card ↥(Yimg hJH hJn F₂) ∣ Nat.card ↥(F₂.subgroupOf H) :=
    Subgroup.card_map_dvd _ _
  have h2 : Nat.card ↥(F₂.subgroupOf H) = Nat.card ↥F₂ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF₂H).toEquiv
  rw [h2] at h1
  exact Odd.of_dvd_nat hodd h1

end Yimg

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
