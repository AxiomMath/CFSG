module

public import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.EtaAbstract
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.IsoOn
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.OuterLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.QzMem
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.Derived
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.ShapeHom

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3 Subgroup

variable {G : Type} [Group G] {a z : G}

theorem exists_eta_Gz_of_std (h : F5Std a z) {w x : G} (hw : IsConj z w) (hx : IsConj a x)
    (hwx : IsConj z (w * x)) :
    ∃ η : G → G, IsIsoOn (Gx w) (Gx w) η ∧ η w = w ∧ η x = x ∧
      ¬ ∃ g ∈ derivedOf (Gxy w x), ∀ y ∈ derivedOf (Gxy w x), η y = g * y * g⁻¹ := by
  classical
  rw [Gxy_comm w x]
  haveI : Finite G := h.finite
  have hF : F5Std a w := h.of_isConj (IsConj.refl a) hw
  have hcomm : w * x = x * w := h.mul_comm (Or.inr hw) (Or.inl hx) (Or.inr hwx)
  have hxw : x ∈ Gx w := mem_Gx.2 hcomm
  have hxQ : x ∉ Qz w := not_mem_Qz_of_isConj_mul h hw hx hwx
  have hxD : x ∉ derivedOf (Gx w) := not_mem_derived_of_outer_2A hF hxw hxQ hx
  have hx2 : x ^ 2 = 1 := by
    have h2 := pow_orderOf_eq_one x
    rwa [h.orderOf_eq_two (Or.inl hx)] at h2
  have hwx' : IsConj w (x * w) := by
    have h1 : IsConj w (w * x) := hw.symm.trans hwx
    rwa [hcomm] at h1
  have hY : Y4aStruct a w x := hF.toF5Base.loc.y4a.self.y4a x hxw hx hwx'
  have hM : Nat.card ↥(CFSG.Open.pCoreOf 2 (derivedOf (Gxy x w))) = 16 := by
    have h16 : Nat.card ↥(CFSG.Open.pCoreOf 2 (derivedOf (Gxy x w))) = 2 ^ 4 := hY.orth.1.2
    rw [h16]
    norm_num
  obtain ⟨π, hπsurj, hπker, hπab⟩ := y4a_exists_hom hY.shape
  obtain ⟨-, -, hψdata⟩ := y4a_derived_of_hom π hπsurj hπker hπab hM
  obtain ⟨ψ₀, hψsurj, hψker⟩ := hψdata
  obtain ⟨Q, hQn, hAH⟩ := hF.loc.gz9.self.aschbacher
  haveI : Q.Normal := hQn
  let xC : ↥(Gx w) := ⟨x, hxw⟩
  have hxC : xC ∉ _root_.commutator ↥(Gx w) := fun hmem =>
    hxD (mem_derivedOf_iff.mpr ⟨hxw, hmem⟩)
  have hxC2 : xC ^ 2 = 1 := Subtype.ext (by simpa using hx2)
  have hXle : Gxy x w ≤ Gx w := by
    rw [Gxy_eq_inf]
    exact inf_le_right
  have hY'le : derivedOf (Gxy x w) ≤ derivedOf (Gx w) := derivedOf_mono hXle
  have hY'Gx : derivedOf (Gxy x w) ≤ Gx w := (derivedOf_le _).trans hXle
  let YC : Subgroup ↥(Gx w) := (derivedOf (Gxy x w)).subgroupOf (Gx w)
  have hYL : YC ≤ _root_.commutator ↥(Gx w) := by
    intro y hy
    obtain ⟨hyG, hyc⟩ := mem_derivedOf_iff.mp (hY'le (Subgroup.mem_subgroupOf.mp hy))
    exact hyc
  have hYx : ∀ y ∈ YC, xC * y = y * xC := by
    intro y hy
    have hyX : (y : G) ∈ Gxy x w := derivedOf_le _ (Subgroup.mem_subgroupOf.mp hy)
    apply Subtype.ext
    exact mem_Gx.mp (mem_Gxy.mp hyX).1
  let ψC : ↥YC →* alternatingGroup (Fin 5) :=
    ψ₀.comp (Subgroup.subgroupOfEquivOfLe hY'Gx).toMonoidHom
  have hψs : Function.Surjective ψC :=
    hψsurj.comp (Subgroup.subgroupOfEquivOfLe hY'Gx).surjective
  have hψk : ∀ y : ↥YC, (y : ↥(Gx w)) ∈ Q → ψC y = 1 := by
    intro y hyQ
    have hyY' : ((y : ↥(Gx w)) : G) ∈ derivedOf (Gxy x w) := Subgroup.mem_subgroupOf.mp y.2
    let T : Subgroup ↥(derivedOf (Gxy x w)) := Q.comap (Subgroup.inclusion hY'Gx)
    have hTn : T.Normal := Subgroup.Normal.comap inferInstance _
    have hTp : IsPGroup 2 ↥T :=
      hAH.plus.isExtraspecialPGroup.1.comap_of_injective _ (Subgroup.inclusion_injective hY'Gx)
    have hTle : T ≤ CFSG.pCore 2 ↥(derivedOf (Gxy x w)) :=
      CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hTn hTp
    have hl₀ : (⟨(y : G), hyY'⟩ : ↥(derivedOf (Gxy x w))) ∈
        CFSG.pCore 2 ↥(derivedOf (Gxy x w)) := hTle hyQ
    exact (hψker ⟨(y : G), hyY'⟩).mpr (Subgroup.mem_map.mpr ⟨_, hl₀, rfl⟩)
  obtain ⟨η₀, hη₀x, hη₀c, hη₀n⟩ := EtaGz.AschbacherHyp.exists_aut_fix_not_inner hAH hxC hxC2 YC
    hYL hYx ψC hψs hψk
  obtain ⟨η, hη, hηeq⟩ := exists_isIsoOn_of_mulEquiv η₀
  refine ⟨η, hη, ?_, ?_, ?_⟩
  ·
    have hwC : ∀ c : ↥(Gx w), c * (⟨w, self_mem_Gx w⟩ : ↥(Gx w)) = ⟨w, self_mem_Gx w⟩ * c := by
      intro c
      apply Subtype.ext
      exact (mem_Gx.mp c.2).symm
    have h1 := hηeq ⟨w, self_mem_Gx w⟩
    rw [hη₀c _ hwC] at h1
    exact h1
  · have h1 := hηeq xC
    rw [hη₀x] at h1
    exact h1
  · rintro ⟨g, hg, hgη⟩
    refine hη₀n ⟨⟨g, hY'Gx hg⟩, Subgroup.mem_subgroupOf.mpr hg, fun y hy => ?_⟩
    apply Subtype.ext
    rw [← hηeq y]
    exact hgη (y : G) (Subgroup.mem_subgroupOf.mp hy)

end CFSG.EvenSporadicStandard.HNRecog.Section4
