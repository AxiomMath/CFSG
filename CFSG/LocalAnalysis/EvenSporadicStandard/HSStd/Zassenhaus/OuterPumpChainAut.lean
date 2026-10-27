module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.DiagonalLink
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Props

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

section Aut

variable {L : Type} [Group L]

theorem aut_mem_center (σ : MulAut L) {y : L} (hy : y ∈ center L) : σ y ∈ center L := by
  rw [mem_center_iff] at hy ⊢
  intro g
  have h := congrArg σ (hy (σ.symm g))
  simpa using h

theorem map_center_aut (σ : MulAut L) : (center L).map σ.toMonoidHom = center L := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact aut_mem_center σ hy
  · intro hx
    exact ⟨σ.symm x, aut_mem_center σ.symm hx, by simp⟩

@[expose] def quotAut (σ : MulAut L) : MulAut (L ⧸ center L) :=
  QuotientGroup.congr (center L) (center L) σ (map_center_aut σ)

theorem quotAut_mk (σ : MulAut L) (x : L) :
    quotAut σ (QuotientGroup.mk x) = QuotientGroup.mk (σ x) :=
  QuotientGroup.congr_mk _ _ _ _ _

theorem quotAut_sq {σ : MulAut L} (hσ : ∀ x, σ (σ x) = x) : quotAut σ * quotAut σ = 1 := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H x => simp [quotAut_mk, hσ]

theorem mem_autCentralizer_quotAut_iff (σ : MulAut L) (x : L) :
    (QuotientGroup.mk x : L ⧸ center L) ∈ autCentralizer (quotAut σ) ↔
      (σ x)⁻¹ * x ∈ center L := by
  show quotAut σ (QuotientGroup.mk x) = QuotientGroup.mk x ↔ _
  rw [quotAut_mk, QuotientGroup.eq]

theorem exists_central_mul {σ : MulAut L} {x : L} (h : (σ x)⁻¹ * x ∈ center L) :
    ∃ z ∈ center L, σ x = z * x := by
  refine ⟨((σ x)⁻¹ * x)⁻¹, inv_mem h, ?_⟩
  have h2 : x * ((σ x)⁻¹ * x)⁻¹ = ((σ x)⁻¹ * x)⁻¹ * x := mem_center_iff.1 (inv_mem h) x
  rw [← h2]
  simp

@[expose] def fixPre (σ : MulAut L) : Subgroup L :=
  (autCentralizer (quotAut σ)).comap (QuotientGroup.mk' (center L))

theorem mem_fixPre_iff (σ : MulAut L) (x : L) : x ∈ fixPre σ ↔ (σ x)⁻¹ * x ∈ center L :=
  mem_autCentralizer_quotAut_iff σ x

theorem autCentralizer_le_fixPre (σ : MulAut L) : autCentralizer σ ≤ fixPre σ := by
  intro x hx
  rw [mem_fixPre_iff]
  have h : σ x = x := hx
  rw [h, inv_mul_cancel]
  exact one_mem _

theorem normal_autCentralizer_fixPre (σ : MulAut L) :
    ((autCentralizer σ).subgroupOf (fixPre σ)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : σ (n : L) = n := hn
  obtain ⟨z, hz, hzg⟩ := exists_central_mul (mem_fixPre_iff σ _ |>.1 g.2)
  rw [Subgroup.mem_subgroupOf]
  show σ ((g : L) * n * (g : L)⁻¹) = (g : L) * n * (g : L)⁻¹
  rw [map_mul, map_mul, map_inv, hn', hzg]
  have hc := mem_center_iff.1 hz ((g : L) * n * (g : L)⁻¹)
  calc z * g * n * (z * g)⁻¹ = z * ((g : L) * n * (g : L)⁻¹) * z⁻¹ := by group
    _ = ((g : L) * n * (g : L)⁻¹) * z * z⁻¹ := by rw [← hc]
    _ = (g : L) * n * (g : L)⁻¹ := by group

end Aut

section Sub

theorem isSubnormal_subgroupOf_trans {Y : Type*} [Group Y] {H R D : Subgroup Y} (hHR : H ≤ R)
    (hRD : R ≤ D) (hsub : (H.subgroupOf R).IsSubnormal) (hN : (R.subgroupOf D).Normal) :
    (H.subgroupOf D).IsSubnormal := by
  have hle : H.subgroupOf D ≤ R.subgroupOf D := fun x hx => hHR hx
  refine Subgroup.IsSubnormal.trans hle ?_ hN.isSubnormal
  let e : ↥R ≃* ↥(R.subgroupOf D) := (Subgroup.subgroupOfEquivOfLe hRD).symm
  have h2 := hsub.map (f := e.toMonoidHom) e.surjective
  convert h2 using 1
  ext ⟨⟨x, hxD⟩, hxR⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · intro hxH
    refine ⟨⟨x, hxR⟩, ?_, rfl⟩
    exact hxH
  · rintro ⟨⟨y, hyR⟩, hy, hyx⟩
    have : y = x := congrArg (fun q : ↥(R.subgroupOf D) => ((q : ↥D) : Y)) hyx
    subst this
    exact hy

end Sub

section Range

variable {L : Type} [Group L] {K0 : Type} [Group K0]

theorem range_le_autCentralizer_quotAut (σ : MulAut L) (ι : K0 →* L)
    (hfix : ι.range ≤ autCentralizer σ) :
    ((QuotientGroup.mk' (center L)).comp ι).range ≤ autCentralizer (quotAut σ) := by
  rintro _ ⟨k, rfl⟩
  show quotAut σ (QuotientGroup.mk (ι k)) = QuotientGroup.mk (ι k)
  rw [quotAut_mk]
  have h : σ (ι k) = ι k := hfix ⟨k, rfl⟩
  rw [h]

theorem isSubnormal_range_quotAut (σ : MulAut L) (ι : K0 →* L) (hfix : ι.range ≤ autCentralizer σ)
    (hsub : (ι.range.subgroupOf (autCentralizer σ)).IsSubnormal) :
    (((QuotientGroup.mk' (center L)).comp ι).range.subgroupOf
      (autCentralizer (quotAut σ))).IsSubnormal := by
  have h1 : (ι.range.subgroupOf (fixPre σ)).IsSubnormal :=
    isSubnormal_subgroupOf_trans hfix (autCentralizer_le_fixPre σ) hsub
      (normal_autCentralizer_fixPre σ)
  let ψ : ↥(fixPre σ) →* ↥(autCentralizer (quotAut σ)) :=
    (QuotientGroup.mk' (center L)).subgroupComap (autCentralizer (quotAut σ))
  have hψ : Function.Surjective ψ :=
    MonoidHom.subgroupComap_surjective _ _ (QuotientGroup.mk'_surjective _)
  have h2 := h1.map hψ
  convert h2 using 1
  ext c
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨⟨ι k, ?_⟩, ⟨k, rfl⟩, ?_⟩
    · have : (QuotientGroup.mk' (center L)) (ι k) ∈ autCentralizer (quotAut σ) := by
        rw [MonoidHom.comp_apply] at hk
        exact hk ▸ c.2
      exact this
    · apply Subtype.ext
      exact hk
  · rintro ⟨d, ⟨k, hk⟩, rfl⟩
    refine ⟨k, ?_⟩
    simp only [MonoidHom.comp_apply, hk]
    rfl

theorem range_eq_top_of_quotAut_eq_one (hLq : CFSG.IsQuasisimple L) (hK0 : CFSG.IsQuasisimple K0)
    (σ : MulAut L) (ι : K0 →* L) (hι : Function.Injective ι)
    (hsub : (ι.range.subgroupOf (autCentralizer σ)).IsSubnormal) (h1 : quotAut σ = 1) :
    ι.range = ⊤ := by
  have hcent : ∀ x : L, (σ x)⁻¹ * x ∈ center L := by
    intro x
    have := congrArg (fun f : MulAut (L ⧸ center L) => f (QuotientGroup.mk x)) h1
    simp only [quotAut_mk, MulAut.one_apply] at this
    exact QuotientGroup.eq.1 this
  have hcomm : ∀ x y : L, σ ⁅x, y⁆ = ⁅x, y⁆ := by
    intro x y
    obtain ⟨z, hz, hzx⟩ := exists_central_mul (hcent x)
    obtain ⟨w, hw, hwy⟩ := exists_central_mul (hcent y)
    rw [map_commutatorElement, hzx, hwy, commutatorElement_mul_central_of_mem hz hw]
  have hperf : commutator L = ⊤ := hLq.1.commutator_eq_top
  have htopC : autCentralizer σ = ⊤ := by
    rw [eq_top_iff, ← hperf, _root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact hcomm x y
  have hle : ι.range ≤ autCentralizer σ := htopC ▸ le_top
  have hnormal : (autCentralizer σ).Normal := by
    rw [htopC]
    infer_instance
  have hrsub : ι.range.IsSubnormal :=
    Subgroup.IsSubnormal.trans hle hsub hnormal.isSubnormal
  have := hK0.1
  have hperfR : Group.IsPerfect ↥ι.range := Group.IsPerfect.ofSurjective ι.rangeRestrict_surjective
  have hne : ι.range ≠ ⊥ := by
    intro hbot
    obtain ⟨-, -, a, b, hab⟩ := hK0
    have hx : ∀ x : K0, x = 1 := by
      intro x
      have hmem : ι x ∈ ι.range := ⟨x, rfl⟩
      rw [hbot, mem_bot] at hmem
      exact hι (hmem.trans (map_one ι).symm)
    have hq1 : ∀ q : K0 ⧸ center K0, q = 1 := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H x => rw [hx x]; rfl
    exact hab (by rw [hq1 a, hq1 b])
  exact eq_top_of_isSubnormal_of_perfect hLq hrsub hperfR hne

end Range

section Center

variable {K0 : Type} [Group K0]

theorem rangeRestrict_mem_center_iff (hq : CFSG.IsQuasisimple K0) {Y : Type*} [Group Y]
    (φ : K0 →* Y) (hker : φ.ker ≤ center K0) (a : K0) :
    φ.rangeRestrict a ∈ center ↥φ.range ↔ a ∈ center K0 := by
  constructor
  · intro ha
    have hZ := center_quotient_center_eq_bot hq
    have hmem : (QuotientGroup.mk a : K0 ⧸ center K0) ∈ center (K0 ⧸ center K0) := by
      rw [mem_center_iff]
      intro q
      induction q using QuotientGroup.induction_on with
      | H b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        apply hker
        have h : φ b * φ a = φ a * φ b := by
          have := congrArg Subtype.val ((mem_center_iff.1 ha) (φ.rangeRestrict b))
          simpa using this
        have e1 : φ ((b * a)⁻¹ * (a * b)) = (φ b * φ a)⁻¹ * (φ a * φ b) := by
          simp only [map_mul, map_inv, mul_inv_rev]
        rw [MonoidHom.mem_ker, e1, h, inv_mul_cancel]
    rw [hZ, mem_bot] at hmem
    exact QuotientGroup.eq_one_iff _ |>.1 hmem
  · intro ha
    rw [mem_center_iff]
    intro y
    obtain ⟨b, rfl⟩ := φ.rangeRestrict_surjective y
    rw [← map_mul, ← map_mul, (mem_center_iff.1 ha) b]

theorem isPGroup_center_range (hq : CFSG.IsQuasisimple K0) {Y : Type*} [Group Y] (φ : K0 →* Y)
    (hker : φ.ker ≤ center K0) (h2 : IsPGroup 2 ↥(center K0)) : IsPGroup 2 ↥(center ↥φ.range) := by
  intro x
  obtain ⟨a, ha⟩ := φ.rangeRestrict_surjective (x : ↥φ.range)
  have hac : a ∈ center K0 := (rangeRestrict_mem_center_iff hq φ hker a).1 (ha ▸ x.2)
  obtain ⟨k, hk⟩ := h2 ⟨a, hac⟩
  refine ⟨k, ?_⟩
  apply Subtype.ext
  have h3 : a ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h4 : (x : ↥φ.range) ^ (2 ^ k) = 1 := by rw [← ha, ← map_pow, h3, map_one]
  exact h4

end Center

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
