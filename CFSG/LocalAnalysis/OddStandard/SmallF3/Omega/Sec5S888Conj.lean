module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L67b

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem twoRes_map (H : Subgroup G) (φ : G ≃* G) :
    twoRes (H.map φ.toMonoidHom) = (twoRes H).map φ.toMonoidHom := by
  have hset : φ.toMonoidHom '' {x | x ∈ H ∧ Odd (orderOf x)}
      = {x | x ∈ H.map φ.toMonoidHom ∧ Odd (orderOf x)} := by
    ext y
    constructor
    · rintro ⟨x, hxS, rfl⟩
      refine ⟨Subgroup.mem_map.mpr ⟨x, hxS.1, rfl⟩, ?_⟩
      show Odd (orderOf (φ x))
      rw [MulEquiv.orderOf_eq φ x]
      exact hxS.2
    · rintro ⟨hyH, hyodd⟩
      obtain ⟨x, hxH, rfl⟩ := Subgroup.mem_map.mp hyH
      refine ⟨x, ⟨hxH, ?_⟩, rfl⟩
      show Odd (orderOf x)
      rw [← MulEquiv.orderOf_eq φ x]
      exact hyodd
  unfold twoRes
  rw [MonoidHom.map_closure]
  congr 1
  exact hset.symm

private theorem centerIn_conjugate (L : Subgroup G) (g : G) :
    centerIn (CFSG.conjugate L g) = CFSG.conjugate (centerIn L) g := by
  let φ : G ≃* G := MulAut.conj g⁻¹
  let e : ↥L ≃* ↥(L.map φ.toMonoidHom) := L.equivMapOfInjective φ.toMonoidHom φ.injective
  have hkey := Subgroup.map_center_eq e
  unfold centerIn CFSG.conjugate
  rw [← hkey, Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem inSubgroup_layer_map (H : Subgroup G) (φ : G ≃* G) :
    CFSG.inSubgroup CFSG.layer (H.map φ.toMonoidHom) =
      (CFSG.inSubgroup CFSG.layer H).map φ.toMonoidHom := by
  let e : ↥H ≃* ↥(H.map φ.toMonoidHom) := H.equivMapOfInjective φ.toMonoidHom φ.injective
  have hkey := CFSG.WholeGroup.layer_map_mulEquiv e
  unfold CFSG.inSubgroup
  rw [← hkey, Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem layerCent_conjugate (L : Subgroup G) (r g : G) :
    layerCent (CFSG.conjugate L g) (g⁻¹ * r * g) =
      CFSG.conjugate (layerCent L r) g := by
  let φ : G ≃* G := MulAut.conj g⁻¹
  let H : Subgroup G := L ⊓ centralizer ({r} : Set G)
  have h1 : H.map φ.toMonoidHom =
      CFSG.conjugate L g ⊓ CFSG.conjugate (centralizer ({r} : Set G)) g := by
    unfold H CFSG.conjugate
    exact Subgroup.map_inf L (centralizer ({r} : Set G)) φ.toMonoidHom φ.injective
  have hH : CFSG.conjugate L g ⊓ centralizer ({g⁻¹ * r * g} : Set G) =
      H.map φ.toMonoidHom := by
    rw [h1, conjugate_centralizer_singleton r g]
  unfold layerCent
  rw [hH]
  exact inSubgroup_layer_map H φ

private theorem sec5RCtx_conj [Finite G] {t : G} {L S : Subgroup G} {z r : G}
    {B A : Subgroup G} (hc : Sec5RCtx G t L S z r B A) (g : G) :
    Sec5RCtx G (g⁻¹ * t * g) (CFSG.conjugate L g) (CFSG.conjugate S g) (g⁻¹ * z * g)
      (g⁻¹ * r * g) (CFSG.conjugate B g) (CFSG.conjugate A g) := by
  let φ : G ≃* G := MulAut.conj g⁻¹
  have hcent : (centralizer ({r} : Set G)).map φ.toMonoidHom =
      centralizer ({g⁻¹ * r * g} : Set G) := by
    simpa only [CFSG.conjugate] using conjugate_centralizer_singleton r g
  have hlayer : (layerCent L r).map φ.toMonoidHom =
      layerCent (CFSG.conjugate L g) (g⁻¹ * r * g) := by
    simpa only [CFSG.conjugate] using (layerCent_conjugate L r g).symm
  have hzp : (zpowers t).map φ.toMonoidHom = zpowers (g⁻¹ * t * g) := by
    rw [MonoidHom.map_zpowers]
    show zpowers ((MulAut.conj g⁻¹) t) = zpowers (g⁻¹ * t * g)
    rw [MulAut.conj_apply, inv_inv]
  have hconj_r : ∃ g₁ : G, g₁⁻¹ * (g⁻¹ * t * g) * g₁ = g⁻¹ * r * g := by
    obtain ⟨g₀, hg₀⟩ := hc.conj_r
    exact ⟨g⁻¹ * g₀ * g, by rw [← hg₀]; group⟩
  have htype_r : ∃ α : ℤˣ,
      InducesTypeSome (CFSG.conjugate L g) (g⁻¹ * r * g) 6 (-1) 1 α := by
    obtain ⟨α, hα⟩ := hc.type_r
    exact ⟨α, inducesTypeSome_conjugate hα g⟩
  have hB_le : CFSG.conjugate B g ≤
      CFSG.conjugate L g ⊓ centralizer ({g⁻¹ * r * g} : Set G) := by
    have hmap := Subgroup.map_mono (f := φ.toMonoidHom) hc.B_le
    rw [Subgroup.map_inf _ _ _ φ.injective, hcent] at hmap
    exact hmap
  have hB_E32 : IsElemAb2 (CFSG.conjugate B g) 5 := sec67_isElemAb2_conjugate hc.B_E32 g
  have hB_split : (g⁻¹ * t * g) ∈ CFSG.conjugate B g ∧
      zpowers (g⁻¹ * t * g) ⊓ layerCent (CFSG.conjugate L g) (g⁻¹ * r * g) = ⊥ ∧
      CFSG.conjugate B g = zpowers (g⁻¹ * t * g) ⊔
        (CFSG.conjugate B g ⊓ layerCent (CFSG.conjugate L g) (g⁻¹ * r * g)) := by
    refine ⟨?_, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨t, hc.B_split.1, by simp [φ, MulAut.conj_apply]⟩
    · have hmap := congrArg (Subgroup.map φ.toMonoidHom) hc.B_split.2.1
      rw [Subgroup.map_inf _ _ _ φ.injective, hzp, hlayer, Subgroup.map_bot] at hmap
      simpa [φ, MulAut.conj_apply] using hmap
    · have hmap := congrArg (Subgroup.map φ.toMonoidHom) hc.B_split.2.2
      rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ φ.injective, hzp, hlayer] at hmap
      simpa [CFSG.conjugate, φ, MulAut.conj_apply] using hmap
  have hA_eq : CFSG.conjugate A g = zpowers (g⁻¹ * r * g) ⊔ CFSG.conjugate B g := by
    have hmap := congrArg (Subgroup.map φ.toMonoidHom) hc.A_eq
    rw [Subgroup.map_sup, MonoidHom.map_zpowers] at hmap
    simpa [CFSG.conjugate, φ, MulAut.conj_apply] using hmap
  have hA_le : CFSG.conjugate A g ≤ CFSG.conjugate S g :=
    Subgroup.map_mono (f := φ.toMonoidHom) hc.A_le
  exact { toSec5Ctx := hc.toSec5Ctx.conjugate g
          conj_r := hconj_r
          type_r := htype_r
          B_le := hB_le
          B_E32 := hB_E32
          B_split := hB_split
          A_eq := hA_eq
          A_le := hA_le }

private theorem sec5KCtx_conj [Finite G] {t : G} {L S : Subgroup G} {z r : G}
    {B A K₁ K₂ : Subgroup G} (hc : Sec5KCtx G t L S z r B A K₁ K₂) (g : G) :
    Sec5KCtx G (g⁻¹ * t * g) (CFSG.conjugate L g) (CFSG.conjugate S g) (g⁻¹ * z * g)
      (g⁻¹ * r * g) (CFSG.conjugate B g) (CFSG.conjugate A g) (CFSG.conjugate K₁ g)
      (CFSG.conjugate K₂ g) := by
  let φ : G ≃* G := MulAut.conj g⁻¹
  have hcentz : (centralizer ({z} : Set G)).map φ.toMonoidHom =
      centralizer ({g⁻¹ * z * g} : Set G) := by
    simpa only [CFSG.conjugate] using conjugate_centralizer_singleton z g
  have hcentre : centerIn (CFSG.conjugate L g) = zpowers (g⁻¹ * t * g) := by
    have hmap := centerIn_conjugate L g
    rw [hc.centre] at hmap
    rw [show CFSG.conjugate (zpowers t) g = zpowers (g⁻¹ * t * g) by
      simp [CFSG.conjugate, MonoidHom.map_zpowers, MulAut.conj_apply]] at hmap
    exact hmap
  have hpocket₁ : Sl23PocketIn (CFSG.conjugate L g) (g⁻¹ * z * g) (CFSG.conjugate K₁ g) :=
    hc.pocket₁.conjugate g
  have hpocket₂ : Sl23PocketIn (CFSG.conjugate L g) (g⁻¹ * z * g) (CFSG.conjugate K₂ g) :=
    hc.pocket₂.conjugate g
  have hne : CFSG.conjugate K₁ g ≠ CFSG.conjugate K₂ g := by
    intro hEq
    exact hc.ne (Subgroup.map_injective φ.injective hEq)
  have hcomm : ⁅CFSG.conjugate K₁ g, CFSG.conjugate K₂ g⁆ = ⊥ := by
    change ⁅K₁.map φ.toMonoidHom, K₂.map φ.toMonoidHom⁆ = ⊥
    rw [← Subgroup.map_commutator K₁ K₂ φ.toMonoidHom, hc.comm, Subgroup.map_bot]
  have hiso₁ : Nonempty
      (↥(CFSG.conjugate K₁ g) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
    obtain ⟨e⟩ := hc.iso₁
    exact ⟨(K₁.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans e⟩
  have hiso₂ : Nonempty
      (↥(CFSG.conjugate K₂ g) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
    obtain ⟨e⟩ := hc.iso₂
    exact ⟨(K₂.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans e⟩
  have hprod : CFSG.conjugate K₁ g ⊔ CFSG.conjugate K₂ g =
      twoRes (CFSG.conjugate L g ⊓ centralizer ({g⁻¹ * z * g} : Set G)) := by
    have hmap := congrArg (Subgroup.map φ.toMonoidHom) hc.prod
    rw [Subgroup.map_sup, ← twoRes_map (L ⊓ centralizer ({z} : Set G)) φ,
      Subgroup.map_inf _ _ _ φ.injective, hcentz] at hmap
    simpa [CFSG.conjugate, φ, MulAut.conj_apply] using hmap
  exact { toSec5RCtx := sec5RCtx_conj hc.toSec5RCtx g
          centre := hcentre
          pocket₁ := hpocket₁
          pocket₂ := hpocket₂
          ne := hne
          comm := hcomm
          iso₁ := hiso₁
          iso₂ := hiso₂
          prod := hprod }

theorem sec5HCtx_conj {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
    {B A K₁ K₂ : Subgroup G} {h : G} (hc : Sec5HCtx G t L S z r B A K₁ K₂ h) (g : G) :
    Sec5HCtx G (g⁻¹ * t * g) (CFSG.conjugate L g) (CFSG.conjugate S g) (g⁻¹ * z * g)
      (g⁻¹ * r * g) (CFSG.conjugate B g) (CFSG.conjugate A g) (CFSG.conjugate K₁ g)
      (CFSG.conjugate K₂ g) (g⁻¹ * h * g) := by
  let φ : G ≃* G := MulAut.conj g⁻¹
  have hsec5KCtx : Sec5KCtx G (g⁻¹ * t * g) (CFSG.conjugate L g) (CFSG.conjugate S g)
      (g⁻¹ * z * g) (g⁻¹ * r * g) (CFSG.conjugate B g) (CFSG.conjugate A g)
      (CFSG.conjugate K₁ g) (CFSG.conjugate K₂ g) := sec5KCtx_conj hc.toSec5KCtx g
  have hh_mem : g⁻¹ * h * g ∈ normalizer (CFSG.conjugate A g : Set G) := by
    change g⁻¹ * h * g ∈ normalizer (A.map φ.toMonoidHom : Set G)
    have hmap := Subgroup.map_equiv_normalizer_eq A φ
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨h, hc.h_mem, by simp [φ, MulAut.conj_apply]⟩
  have hh_t : (g⁻¹ * h * g)⁻¹ * (g⁻¹ * t * g) * (g⁻¹ * h * g) ∈
      CFSG.conjugate K₁ g ⊔ CFSG.conjugate K₂ g := by
    have h1 : CFSG.conjugate K₁ g ⊔ CFSG.conjugate K₂ g =
        (K₁ ⊔ K₂).map φ.toMonoidHom := by
      change K₁.map φ.toMonoidHom ⊔ K₂.map φ.toMonoidHom =
        (K₁ ⊔ K₂).map φ.toMonoidHom
      rw [Subgroup.map_sup]
    rw [h1]
    refine Subgroup.mem_map.mpr ⟨h⁻¹ * t * h, hc.h_t, ?_⟩
    show (MulAut.conj g⁻¹) (h⁻¹ * t * h) = _
    rw [MulAut.conj_apply]
    group
  have hh_sq : (g⁻¹ * h * g) * (g⁻¹ * h * g) ∈
      centralizer ({g⁻¹ * t * g} : Set G) := by
    rw [← conjugate_centralizer_singleton t g, mem_conjugate_iff]
    show g * ((g⁻¹ * h * g) * (g⁻¹ * h * g)) * g⁻¹ ∈ centralizer ({t} : Set G)
    convert hc.h_sq using 1
    group
  have hh_z : g⁻¹ * h * g ∈ centralizer ({g⁻¹ * z * g} : Set G) := by
    rw [← conjugate_centralizer_singleton z g, mem_conjugate_iff]
    show g * (g⁻¹ * h * g) * g⁻¹ ∈ centralizer ({z} : Set G)
    convert hc.h_z using 1
    group
  exact { toSec5KCtx := hsec5KCtx
          h_mem := hh_mem
          h_t := hh_t
          h_sq := hh_sq
          h_z := hh_z }

end CFSG.OddStandard.SmallF3.Omega
