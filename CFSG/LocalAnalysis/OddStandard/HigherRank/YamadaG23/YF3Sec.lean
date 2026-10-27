module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3D8

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

theorem isE2_image {A : Type} [Group A] [Finite A] {Q K : Subgroup A} [Q.Normal] (hQK : Q ≤ K)
    (hsq : ∀ x ∈ K, x ^ 2 ∈ Q) (hidx : Q.relIndex K = 4) :
    IsE 2 ↥(K.map (QuotientGroup.mk' Q)) := by
  have hsq' : ∀ y : ↥(K.map (QuotientGroup.mk' Q)), y ^ 2 = 1 := by
    intro y
    obtain ⟨x, hxK, hxy⟩ := Subgroup.mem_map.mp y.property
    have h : (y : A ⧸ Q) ^ 2 = 1 := by
      rw [← hxy, ← map_pow]
      exact (QuotientGroup.eq_one_iff (x ^ 2)).mpr (hsq x hxK)
    exact Subtype.ext h
  have hcard : Nat.card ↥(K.map (QuotientGroup.mk' Q)) = 4 := by
    rw [← MonoidHom.domRestrict_range K (QuotientGroup.mk' Q),
      ← Subgroup.index_ker ((QuotientGroup.mk' Q).domRestrict K),
      MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
    exact hidx
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [isMulCommutative_iff_of_setLike]
    intro a _ b _
    have ha : a ^ 2 = 1 := hsq' a
    have hb : b ^ 2 = 1 := hsq' b
    have hab : (a * b) ^ 2 = 1 := hsq' (a * b)
    have hab' : a * b * (a * b) = 1 := by simpa [pow_two] using hab
    calc a * b = (a * b)⁻¹ := (mul_eq_one_iff_eq_inv.mp hab')
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by
          rw [inv_eq_of_mul_eq_one_right (show b * b = 1 by simpa [pow_two] using hb),
            inv_eq_of_mul_eq_one_left (show a * a = 1 by simpa [pow_two] using ha)]
  · intro x _
    exact hsq' x
  · rw [hcard]
    norm_num

theorem map_mk_inj {A : Type} [Group A] {Q K K' : Subgroup A} [Q.Normal] (h : Q ≤ K)
    (h' : Q ≤ K') (hmap : K.map (QuotientGroup.mk' Q) = K'.map (QuotientGroup.mk' Q)) :
    K = K' := by
  have hker : (QuotientGroup.mk' Q).ker ≤ K := by rw [QuotientGroup.ker_mk']; exact h
  have hker' : (QuotientGroup.mk' Q).ker ≤ K' := by rw [QuotientGroup.ker_mk']; exact h'
  calc K = (K.map (QuotientGroup.mk' Q)).comap (QuotientGroup.mk' Q) :=
        (Subgroup.comap_map_eq_self hker).symm
    _ = (K'.map (QuotientGroup.mk' Q)).comap (QuotientGroup.mk' Q) := by rw [hmap]
    _ = K' := Subgroup.comap_map_eq_self hker'

theorem secProp_iso {G : Type} [Group G] [Finite G] {C P : Subgroup G} {W : Type} [Group W]
    (f : ↥C →* W) (hf : Function.Surjective f) (hker : ∀ c : ↥C, f c = 1 ↔ (c : G) ∈ P) :
    SecProp C P (fun Y _ _ π => ∃ φ : Y ≃* W, ∀ c : ↥C, φ (π c) = f c) := by
  have hker_eq : P.subgroupOf C = f.ker := by
    ext c
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact (hker c).symm
  haveI : (P.subgroupOf C).Normal := by
    rw [hker_eq]
    infer_instance
  refine ⟨inferInstance, (QuotientGroup.quotientMulEquivOfEq hker_eq).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf), ?_⟩
  intro c
  exact QuotientGroup.kerLift_mk f c

theorem secProp_d8 {G : Type} [Group G] [Finite G] {T₂ Q K₁ K₂ : Subgroup G} (hQT : Q ≤ T₂)
    (hQn : ∀ x ∈ T₂, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) (hK₁ : K₁ ≤ T₂) (hK₂ : K₂ ≤ T₂)
    (hQK₁ : Q ≤ K₁) (hQK₂ : Q ≤ K₂) (hcard : Q.relIndex T₂ = 8)
    (hnc : ∃ x ∈ T₂, ∃ y ∈ T₂, x * y * x⁻¹ * y⁻¹ ∉ Q)
    (hsq₁ : ∀ x ∈ K₁, x ^ 2 ∈ Q) (hsq₂ : ∀ x ∈ K₂, x ^ 2 ∈ Q)
    (hi₁ : Q.relIndex K₁ = 4) (hi₂ : Q.relIndex K₂ = 4) (hne : ¬ K₂ ≤ K₁) :
    SecProp T₂ Q (fun Y _ _ π =>
      Nonempty (Y ≃* DihedralGroup 4) ∧
        {V : Subgroup Y | IsE 2 ↥V} =
          {(K₁.subgroupOf T₂).map π, (K₂.subgroupOf T₂).map π}) := by
  have hQn' : ∀ h k, h ∈ Q → k ∈ T₂ → k * h * k⁻¹ ∈ Q :=
    fun h k hh hk => hQn k hk h hh
  haveI : (Q.subgroupOf T₂).Normal := (Subgroup.normal_subgroupOf_iff hQT).mpr hQn'
  let D := ↥T₂ ⧸ Q.subgroupOf T₂
  let π : ↥T₂ →* D := QuotientGroup.mk' (Q.subgroupOf T₂)
  have hD : Nat.card D = 8 := by
    change Nat.card (↥T₂ ⧸ Q.subgroupOf T₂) = 8
    rw [← Subgroup.index_eq_card]
    exact hcard
  have hnc' : ∃ x y : D, x * y ≠ y * x := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    refine ⟨π ⟨x, hx⟩, π ⟨y, hy⟩, ?_⟩
    intro hcomm
    apply hxy
    have hkey : π ⁅(⟨x, hx⟩ : ↥T₂), (⟨y, hy⟩ : ↥T₂)⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
    have hmem : ⁅(⟨x, hx⟩ : ↥T₂), (⟨y, hy⟩ : ↥T₂)⁆ ∈ Q.subgroupOf T₂ :=
      (QuotientGroup.eq_one_iff _).mp hkey
    simpa [commutatorElement_def] using Subgroup.mem_subgroupOf.mp hmem
  have h₁ : IsE 2 ↥((K₁.subgroupOf T₂).map (QuotientGroup.mk' (Q.subgroupOf T₂))) :=
    isE2_image (Subgroup.subgroupOf_mono T₂ hQK₁)
      (fun x hx => by
        rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
        exact hsq₁ (x : G) (Subgroup.mem_subgroupOf.mp hx))
      (by rw [Subgroup.relIndex_subgroupOf hK₁]; exact hi₁)
  have h₂ : IsE 2 ↥((K₂.subgroupOf T₂).map (QuotientGroup.mk' (Q.subgroupOf T₂))) :=
    isE2_image (Subgroup.subgroupOf_mono T₂ hQK₂)
      (fun x hx => by
        rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
        exact hsq₂ (x : G) (Subgroup.mem_subgroupOf.mp hx))
      (by rw [Subgroup.relIndex_subgroupOf hK₂]; exact hi₂)
  have hne' : (K₁.subgroupOf T₂).map (QuotientGroup.mk' (Q.subgroupOf T₂)) ≠
      (K₂.subgroupOf T₂).map (QuotientGroup.mk' (Q.subgroupOf T₂)) := by
    intro hmap
    have hK : K₁.subgroupOf T₂ = K₂.subgroupOf T₂ :=
      map_mk_inj (Subgroup.subgroupOf_mono T₂ hQK₁) (Subgroup.subgroupOf_mono T₂ hQK₂) hmap
    apply hne
    intro k hk
    have hmem : (⟨k, hK₂ hk⟩ : ↥T₂) ∈ K₂.subgroupOf T₂ := hk
    rw [← hK] at hmem
    simpa using Subgroup.mem_subgroupOf.mp hmem
  exact ⟨inferInstance, d8_of_two_klein hD hnc' h₁ h₂ hne'⟩

end CFSG.OddStandard.HigherRank.YamadaG23
