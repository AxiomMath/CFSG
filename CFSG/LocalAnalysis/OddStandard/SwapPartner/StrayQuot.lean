module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.AutProdLemmas
public import CFSG.Foundations.Basic

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

@[expose] def strayCenterIn {Y : Type*} [Group Y] (J : Subgroup Y) : Subgroup Y :=
  (center ↥J).map J.subtype

variable {Y : Type*} [Group Y]

theorem strayCenterIn_le (J : Subgroup Y) : strayCenterIn J ≤ J :=
  Subgroup.map_subtype_le (center ↥J)

instance normal_strayCenterIn (J : Subgroup Y) [J.Normal] : (strayCenterIn J).Normal where
  conj_mem := by
    intro y hy g
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    rw [← hzy]
    refine Subgroup.mem_map.mpr
      ⟨⟨g * (z : Y) * g⁻¹, (inferInstance : J.Normal).conj_mem z z.2 g⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro j
    apply Subtype.ext
    have hconj : g⁻¹ * (j : Y) * g ∈ J := by
      simpa using (inferInstance : J.Normal).conj_mem j j.2 g⁻¹
    have hzw : (g⁻¹ * (j : Y) * g) * (z : Y) = (z : Y) * (g⁻¹ * (j : Y) * g) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g⁻¹ * (j : Y) * g, hconj⟩)
    calc (j : Y) * (g * (z : Y) * g⁻¹)
        = g * ((g⁻¹ * (j : Y) * g) * (z : Y)) * g⁻¹ := by group
      _ = g * ((z : Y) * (g⁻¹ * (j : Y) * g)) * g⁻¹ := by rw [hzw]
      _ = (g * (z : Y) * g⁻¹) * (j : Y) := by group

theorem normal_map_strayCenterIn (J : Subgroup Y) [J.Normal] :
    (J.map (QuotientGroup.mk' (strayCenterIn J))).Normal :=
  Subgroup.Normal.map (inferInstance : J.Normal) (QuotientGroup.mk' (strayCenterIn J))
    (QuotientGroup.mk'_surjective (strayCenterIn J))

theorem card_inf_centralizer_map_le [Finite Y] (J : Subgroup Y) [J.Normal] (t : Y) :
    Nat.card ↥(J.map (QuotientGroup.mk' (strayCenterIn J)) ⊓
        centralizer ({(QuotientGroup.mk t : Y ⧸ strayCenterIn J)} : Set (Y ⧸ strayCenterIn J))) ≤
      Nat.card ↥(J ⊓ centralizer ({t} : Set Y)) := by
  let Z : Subgroup Y := strayCenterIn J
  let f : Y →* Y ⧸ Z := QuotientGroup.mk' Z
  let B : Subgroup (Y ⧸ Z) :=
    J.map f ⊓ centralizer ({(f t : Y ⧸ Z)} : Set (Y ⧸ Z))
  let P : Subgroup Y := B.comap f
  change Nat.card ↥B ≤ Nat.card ↥(J ⊓ centralizer ({t} : Set Y))
  have hker : f.ker = Z := QuotientGroup.ker_mk' Z
  have hB : B ≤ f.range := by
    have : f.range = ⊤ := QuotientGroup.range_mk' Z
    rw [this]
    exact le_top
  have hcardP : Nat.card ↥P = Nat.card ↥B * Nat.card ↥Z := by
    have h := card_comap_eq_of_le_range f B hB
    rw [hker] at h
    exact h
  have hP_J : P ≤ J := by
    intro y hy
    have hyB : f y ∈ B := Subgroup.mem_comap.mp hy
    obtain ⟨j, hj, hjy⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp hyB).1
    have hmem : j⁻¹ * y ∈ Z := by
      rw [← hker, MonoidHom.mem_ker]
      show f (j⁻¹ * y) = 1
      rw [map_mul, map_inv, hjy]
      exact inv_mul_cancel _
    have hy_eq : y = j * (j⁻¹ * y) := by group
    rw [hy_eq]
    exact J.mul_mem hj ((strayCenterIn_le J) (by simpa [Z] using hmem))
  have hcomm : ∀ z ∈ P, z * t * z⁻¹ * t⁻¹ ∈ Z := by
    intro z hz
    have hzB : f z ∈ B := Subgroup.mem_comap.mp hz
    have hzC : f z ∈ centralizer ({(f t : Y ⧸ Z)} : Set (Y ⧸ Z)) :=
      (Subgroup.mem_inf.mp hzB).2
    have hcomm' : f z * f t = f t * f z :=
      Subgroup.mem_centralizer_singleton_iff.mp hzC
    rw [← hker, MonoidHom.mem_ker]
    show f (z * t * z⁻¹ * t⁻¹) = 1
    have hval : f (z * t * z⁻¹ * t⁻¹) = f z * f t * (f z)⁻¹ * (f t)⁻¹ := by
      simp only [map_mul, map_inv]
    rw [hval, hcomm']
    group
  have h1 : Nat.card ↥P ≤ Nat.card ↥(P ⊓ centralizer ({t} : Set Y)) * Nat.card ↥Z :=
    card_le_card_inf_centralizer_mul P Z t hcomm
  have hle : P ⊓ centralizer ({t} : Set Y) ≤ J ⊓ centralizer ({t} : Set Y) :=
    inf_le_inf hP_J le_rfl
  have h2 : Nat.card ↥(P ⊓ centralizer ({t} : Set Y)) ≤
      Nat.card ↥(J ⊓ centralizer ({t} : Set Y)) :=
    Subgroup.card_le_of_le hle
  have h3 : Nat.card ↥B * Nat.card ↥Z ≤
      Nat.card ↥(J ⊓ centralizer ({t} : Set Y)) * Nat.card ↥Z := by
    rw [← hcardP]
    exact h1.trans (Nat.mul_le_mul_right (Nat.card ↥Z) h2)
  have hZpos : 0 < Nat.card ↥Z := by
    haveI : Nonempty ↥Z := ⟨⟨1, Z.one_mem⟩⟩
    exact Nat.card_pos
  exact Nat.le_of_mul_le_mul_right h3 hZpos

private noncomputable def quotCenterEquivMap (J : Subgroup Y) [J.Normal] :
    (↥J ⧸ center ↥J) ≃* ↥(J.map (QuotientGroup.mk' (strayCenterIn J))) := by
  let f : Y →* Y ⧸ strayCenterIn J := QuotientGroup.mk' (strayCenterIn J)
  let g : ↥J →* ↥(J.map f) :=
    (f.domRestrict J).codRestrict (J.map f) fun x => by
      rw [MonoidHom.domRestrict_apply]
      exact Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩
  have hg_apply : ∀ x : ↥J, (g x : Y ⧸ strayCenterIn J) = f (x : Y) := fun _ => rfl
  have hg_surj : Function.Surjective g := by
    intro y
    obtain ⟨x, hx, hfx⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, by
      apply Subtype.ext
      show f x = (y : Y ⧸ strayCenterIn J)
      exact hfx⟩
  have hgker : g.ker = center ↥J := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      rw [Subgroup.mem_center_iff]
      intro y
      have hfx : f (x : Y) = 1 := by
        have := congrArg (fun w : ↥(J.map f) => (w : Y ⧸ strayCenterIn J)) hx
        simpa [hg_apply] using this
      have hxZ : (x : Y) ∈ strayCenterIn J := (QuotientGroup.eq_one_iff (x : Y)).mp hfx
      obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hxZ
      have hcx' : c = x := Subtype.ext hcx
      rw [← hcx']
      exact Subgroup.mem_center_iff.mp hc y
    · intro hx
      have hmem : (x : Y) ∈ strayCenterIn J := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      have hfx : f (x : Y) = 1 := (QuotientGroup.eq_one_iff (x : Y)).mpr hmem
      show g x = 1
      apply Subtype.ext
      rw [hg_apply]
      simpa using hfx
  exact (QuotientGroup.quotientMulEquivOfEq hgker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (φ := g) hg_surj)

theorem isSimpleGroup_map_strayCenterIn {J : Subgroup Y} [J.Normal] (hJ : CFSG.IsQuasisimple ↥J) :
    IsSimpleGroup ↥(J.map (QuotientGroup.mk' (strayCenterIn J))) := by
  haveI : IsSimpleGroup (↥J ⧸ center ↥J) := hJ.2.1
  exact (quotCenterEquivMap J).symm.isSimpleGroup

theorem exists_noncomm_map_strayCenterIn {J : Subgroup Y} [J.Normal] (hJ : CFSG.IsQuasisimple ↥J) :
    ∃ x y : ↥(J.map (QuotientGroup.mk' (strayCenterIn J))), x * y ≠ y * x := by
  obtain ⟨a, b, hab⟩ := hJ.2.2
  refine ⟨quotCenterEquivMap J a, quotCenterEquivMap J b, fun h => hab ?_⟩
  exact (quotCenterEquivMap J).injective (by rw [map_mul, map_mul]; exact h)

end CFSG.OddStandard.AltStdSec.SwapPartner
