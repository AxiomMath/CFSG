module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22N
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitE4Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf15Odd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Act
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Twin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf42Edgeless
public import CFSG.ClassicalInvolution.Q3.TL4D1Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

section Alg

theorem tr3_q8_pair_aux (x ζ : QuaternionGroup 2) (hx : x * x = ζ) (hζ : ζ * ζ = 1) (hζ1 : ζ ≠ 1) :
    ∃ y : QuaternionGroup 2, y * y = ζ ∧ y * x * y⁻¹ = x⁻¹ := by
  revert x ζ
  decide

theorem tr3_exists_inverting {G : Type} [Group G] {R : Subgroup G} (e : ↥R ≃* QuaternionGroup 2)
    {u z : G} (huR : u ∈ R) (hu : u * u = z) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    ∃ w ∈ R, w * w = z ∧ w * u * w⁻¹ = u⁻¹ := by
  have hzR : z ∈ R := hu ▸ R.mul_mem huR huR
  have hx : e ⟨u, huR⟩ * e ⟨u, huR⟩ = e ⟨z, hzR⟩ := by
    rw [← map_mul]
    exact congrArg e (Subtype.ext hu)
  have hζ : e ⟨z, hzR⟩ * e ⟨z, hzR⟩ = 1 := by
    rw [← map_mul]
    exact (congrArg e (Subtype.ext hz2)).trans (map_one e)
  have hζ1 : e ⟨z, hzR⟩ ≠ 1 := by
    intro h
    apply hz1
    have := e.injective (h.trans (map_one e).symm)
    exact congrArg Subtype.val this
  obtain ⟨y, hy, hyx⟩ := tr3_q8_pair_aux _ _ hx hζ hζ1
  refine ⟨(e.symm y : R), (e.symm y).2, ?_, ?_⟩
  · have h1 : e.symm y * e.symm y = ⟨z, hzR⟩ := by
      rw [← map_mul, hy]
      exact e.symm_apply_apply _
    exact congrArg Subtype.val h1
  · have h1 : e.symm y * ⟨u, huR⟩ * (e.symm y)⁻¹ = (⟨u, huR⟩ : R)⁻¹ := by
      have := congrArg e.symm hyx
      rw [map_mul, map_mul, map_inv, map_inv, e.symm_apply_apply] at this
      exact this
    exact congrArg Subtype.val h1

theorem tr3_kk_device {G : Type} [Group G] {z u₁ u₂ w₁ w₂ : G} (hz : z * z = 1)
    (hu₁ : u₁ * u₁ = z) (hu₂ : u₂ * u₂ = z) (hw₁ : w₁ * w₁ = z) (hw₂ : w₂ * w₂ = z)
    (hw₁u₁ : w₁ * u₁ * w₁⁻¹ = u₁⁻¹) (hw₂u₂ : w₂ * u₂ * w₂⁻¹ = u₂⁻¹)
    (h1w₂ : u₁ * w₂ = w₂ * u₁) (h2w₁ : u₂ * w₁ = w₁ * u₂) (hww : w₁ * w₂ = w₂ * w₁) :
    (w₁ * w₂) * (w₁ * w₂) = 1 ∧ (u₁ * u₂) * (w₁ * w₂) = (w₁ * w₂) * (u₁ * u₂) ∧
      u₁ * (w₁ * w₂) * u₁⁻¹ * (w₁ * w₂)⁻¹ = z := by
  have hzw₁ : z * w₁ = w₁ * z := by rw [← hw₁]; group
  have hzu₁ : z * u₁ = u₁ * z := by rw [← hu₁]; group
  have e1 : u₁ * w₁ * u₁⁻¹ = z * w₁ := by
    have h : w₁ * u₁⁻¹ * w₁⁻¹ = u₁ := by
      calc w₁ * u₁⁻¹ * w₁⁻¹ = (w₁ * u₁ * w₁⁻¹)⁻¹ := by group
        _ = u₁ := by rw [hw₁u₁, inv_inv]
    calc u₁ * w₁ * u₁⁻¹ = u₁ * (w₁ * u₁⁻¹ * w₁⁻¹) * w₁ := by group
      _ = u₁ * u₁ * w₁ := by rw [h]
      _ = z * w₁ := by rw [hu₁]
  have e2 : u₂ * w₂ * u₂⁻¹ = z * w₂ := by
    have h : w₂ * u₂⁻¹ * w₂⁻¹ = u₂ := by
      calc w₂ * u₂⁻¹ * w₂⁻¹ = (w₂ * u₂ * w₂⁻¹)⁻¹ := by group
        _ = u₂ := by rw [hw₂u₂, inv_inv]
    calc u₂ * w₂ * u₂⁻¹ = u₂ * (w₂ * u₂⁻¹ * w₂⁻¹) * w₂ := by group
      _ = u₂ * u₂ * w₂ := by rw [h]
      _ = z * w₂ := by rw [hu₂]
  have e3 : u₁ * w₂ * u₁⁻¹ = w₂ := by rw [h1w₂]; group
  have e4 : u₂ * w₁ * u₂⁻¹ = w₁ := by rw [h2w₁]; group
  have hv1 : u₁ * (w₁ * w₂) * u₁⁻¹ = z * (w₁ * w₂) := by
    calc u₁ * (w₁ * w₂) * u₁⁻¹ = (u₁ * w₁ * u₁⁻¹) * (u₁ * w₂ * u₁⁻¹) := by group
      _ = (z * w₁) * w₂ := by rw [e1, e3]
      _ = z * (w₁ * w₂) := by group
  have hv2 : u₂ * (w₁ * w₂) * u₂⁻¹ = z * (w₁ * w₂) := by
    calc u₂ * (w₁ * w₂) * u₂⁻¹ = (u₂ * w₁ * u₂⁻¹) * (u₂ * w₂ * u₂⁻¹) := by group
      _ = w₁ * (z * w₂) := by rw [e4, e2]
      _ = (w₁ * z) * w₂ := by group
      _ = (z * w₁) * w₂ := by rw [hzw₁]
      _ = z * (w₁ * w₂) := by group
  refine ⟨?_, ?_, ?_⟩
  · calc w₁ * w₂ * (w₁ * w₂) = w₁ * (w₂ * w₁) * w₂ := by group
      _ = w₁ * (w₁ * w₂) * w₂ := by rw [hww]
      _ = (w₁ * w₁) * (w₂ * w₂) := by group
      _ = 1 := by rw [hw₁, hw₂, hz]
  · have hc : (u₁ * u₂) * (w₁ * w₂) * (u₁ * u₂)⁻¹ = w₁ * w₂ := by
      calc (u₁ * u₂) * (w₁ * w₂) * (u₁ * u₂)⁻¹ = u₁ * (u₂ * (w₁ * w₂) * u₂⁻¹) * u₁⁻¹ := by group
        _ = u₁ * (z * (w₁ * w₂)) * u₁⁻¹ := by rw [hv2]
        _ = (u₁ * z * u₁⁻¹) * (u₁ * (w₁ * w₂) * u₁⁻¹) := by group
        _ = z * (z * (w₁ * w₂)) := by
          rw [hv1, show u₁ * z * u₁⁻¹ = z by rw [← hzu₁]; group]
        _ = w₁ * w₂ := by rw [← mul_assoc, hz, one_mul]
    calc (u₁ * u₂) * (w₁ * w₂) = ((u₁ * u₂) * (w₁ * w₂) * (u₁ * u₂)⁻¹) * (u₁ * u₂) := by group
      _ = (w₁ * w₂) * (u₁ * u₂) := by rw [hc]
  · rw [hv1]
    group

end Alg

section Syl

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G}
  {z u₁ u₂ u₃ : G}

theorem tr3_exists_sylow_triple (h : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    ∃ R R' R₃ : Subgroup G, IsSylow2In R K ∧ IsSylow2In R' K' ∧ IsSylow2In R₃ K₃ ∧
      u₁ ∈ R ∧ u₂ ∈ R' ∧ u₃ ∈ R₃ ∧ Commutes R R' ∧ Commutes R R₃ ∧ Commutes R' R₃ := by
  have hΩ : HypOmegaGen Ω := h.hyp
  have hK : K ∈ Ω := h.mem
  have hK' : K' ∈ Ω := h.hK'.1
  have hK₃ : K₃ ∈ Ω := h.hK₃.1
  have hz := h.hz
  have hz' := h.hzK'
  have hz₃ := h.hzK₃
  have hne : K' ≠ K := h.hne
  have hne₃ : K₃ ≠ K := h.hK₃K
  have hne₃' : K₃ ≠ K' := h.hK₃K'
  set Z₁ := Subgroup.zpowers u₁ with hZ₁
  set Z₂ := Subgroup.zpowers u₂ with hZ₂
  set Z₃ := Subgroup.zpowers u₃ with hZ₃
  have p₁ : IsPGroup 2 ↥Z₁ := T7A.isPGroup_zpowers_of_orderOf_four h.hu₁.2
  have p₂ : IsPGroup 2 ↥Z₂ := T7A.isPGroup_zpowers_of_orderOf_four h.hu₂.2
  have p₃ : IsPGroup 2 ↥Z₃ := T7A.isPGroup_zpowers_of_orderOf_four h.hu₃.2
  have cm : ∀ {a b : G}, a * b = b * a → Commutes (Subgroup.zpowers a) (Subgroup.zpowers b) := by
    intro a b hab x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute a b from hab) i j).eq
  have c12 : Commutes Z₁ Z₂ := cm h.comm₁₂
  have c13 : Commutes Z₁ Z₃ := cm h.comm₁₃
  have c23 : Commutes Z₂ Z₃ := cm h.comm₂₃
  have hP12 : IsPGroup 2 ↥(Z₁ ⊔ Z₂) :=
    p₁.to_sup_of_normal_right' p₂ (T7A.le_normalizer_of_commutes c12.symm)
  have hP : IsPGroup 2 ↥((Z₁ ⊔ Z₂) ⊔ Z₃) :=
    hP12.to_sup_of_normal_right' p₃ (sup_le (T7A.le_normalizer_of_commutes c13.symm)
      (T7A.le_normalizer_of_commutes c23.symm))
  set P := (Z₁ ⊔ Z₂) ⊔ Z₃ with hPdef
  have hZ₁P : Z₁ ≤ P := le_sup_left.trans le_sup_left
  have hZ₂P : Z₂ ≤ P := le_sup_right.trans le_sup_left
  have hZ₃P : Z₃ ≤ P := le_sup_right
  have hz₁P : u₁ ∈ P := hZ₁P (Subgroup.mem_zpowers u₁)
  have hz₂P : u₂ ∈ P := hZ₂P (Subgroup.mem_zpowers u₂)
  have hz₃P : u₃ ∈ P := hZ₃P (Subgroup.mem_zpowers u₃)
  have nK₁ : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK hK' hne.symm hz hz'
  have nK₂ : K ≤ Subgroup.normalizer (K₃ : Set G) :=
    hΩ.le_normalizer_of_twin hK hK₃ hne₃.symm hz hz₃
  have nK₃ : K' ≤ Subgroup.normalizer (K₃ : Set G) :=
    hΩ.le_normalizer_of_twin hK' hK₃ hne₃'.symm hz' hz₃
  have nK₄ : K' ≤ Subgroup.normalizer (K : Set G) := hΩ.le_normalizer_of_twin hK' hK hne hz' hz
  have nK₅ : K₃ ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_twin hK₃ hK hne₃ hz₃ hz
  have nK₆ : K₃ ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK₃ hK' hne₃' hz₃ hz'
  have hPK : P ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (sup_le ((Subgroup.zpowers_le.mpr h.hu₁.1).trans Subgroup.le_normalizer)
      ((Subgroup.zpowers_le.mpr h.hu₂.1).trans nK₄))
      ((Subgroup.zpowers_le.mpr h.hu₃.1).trans nK₅)
  have hPK' : P ≤ Subgroup.normalizer (K' : Set G) :=
    sup_le (sup_le ((Subgroup.zpowers_le.mpr h.hu₁.1).trans nK₁)
      ((Subgroup.zpowers_le.mpr h.hu₂.1).trans Subgroup.le_normalizer))
      ((Subgroup.zpowers_le.mpr h.hu₃.1).trans nK₆)
  have hPK₃ : P ≤ Subgroup.normalizer (K₃ : Set G) :=
    sup_le (sup_le ((Subgroup.zpowers_le.mpr h.hu₁.1).trans nK₂)
      ((Subgroup.zpowers_le.mpr h.hu₂.1).trans nK₃))
      ((Subgroup.zpowers_le.mpr h.hu₃.1).trans Subgroup.le_normalizer)
  obtain ⟨R, hR, hRfix⟩ := T3.exists_sylow_normalized hP hPK
  have hPR : P ≤ Subgroup.normalizer (R : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (hRfix x hx)
  have hu₁R : u₁ ∈ R := T7B.mem_of_normalizes hR p₁ h.hu₁.1 (hRfix u₁ hz₁P)
  have hP₁ : IsPGroup 2 ↥(P ⊔ R) := hP.to_sup_of_normal_right' hR.2.1 hPR
  have hPR₁ : P ⊔ R ≤ Subgroup.normalizer (K' : Set G) := sup_le hPK' (hR.1.trans nK₁)
  obtain ⟨R', hR', hR'fix⟩ := T3.exists_sylow_normalized hP₁ hPR₁
  have hPR' : P ⊔ R ≤ Subgroup.normalizer (R' : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (hR'fix x hx)
  have hPle₁ : P ≤ P ⊔ R := le_sup_left
  have hu₂R' : u₂ ∈ R' := T7B.mem_of_normalizes hR' p₂ h.hu₂.1 (hR'fix u₂ (hPle₁ hz₂P))
  have hP₂ : IsPGroup 2 ↥((P ⊔ R) ⊔ R') := hP₁.to_sup_of_normal_right' hR'.2.1 hPR'
  have hPR₂ : (P ⊔ R) ⊔ R' ≤ Subgroup.normalizer (K₃ : Set G) :=
    sup_le (sup_le hPK₃ (hR.1.trans nK₂)) (hR'.1.trans nK₃)
  obtain ⟨R₃, hR₃, hR₃fix⟩ := T3.exists_sylow_normalized hP₂ hPR₂
  have hPR₃ : (P ⊔ R) ⊔ R' ≤ Subgroup.normalizer (R₃ : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (hR₃fix x hx)
  have hPle₂ : P ⊔ R ≤ (P ⊔ R) ⊔ R' := le_sup_left
  have hu₃R₃ : u₃ ∈ R₃ :=
    T7B.mem_of_normalizes hR₃ p₃ h.hu₃.1 (hR₃fix u₃ (hPle₂ (hPle₁ hz₃P)))
  have hQ : IsPGroup 2 ↥(((P ⊔ R) ⊔ R') ⊔ R₃) := hP₂.to_sup_of_normal_right' hR₃.2.1 hPR₃
  have hRQ : R ≤ ((P ⊔ R) ⊔ R') ⊔ R₃ := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hR'Q : R' ≤ ((P ⊔ R) ⊔ R') ⊔ R₃ := le_sup_right.trans le_sup_left
  have hR₃Q : R₃ ≤ ((P ⊔ R) ⊔ R') ⊔ R₃ := le_sup_right
  refine ⟨R, R', R₃, hR, hR', hR₃, hu₁R, hu₂R', hu₃R₃, ?_, ?_, ?_⟩
  · exact hΩ.commutes_of_twin_of_isPGroup hK hK' hne.symm hz hz' hR.1 hR'.1
      (hQ.to_le (sup_le hRQ hR'Q))
  · exact hΩ.commutes_of_twin_of_isPGroup hK hK₃ hne₃.symm hz hz₃ hR.1 hR₃.1
      (hQ.to_le (sup_le hRQ hR₃Q))
  · exact hΩ.commutes_of_twin_of_isPGroup hK' hK₃ hne₃'.symm hz' hz₃ hR'.1 hR₃.1
      (hQ.to_le (sup_le hR'Q hR₃Q))

theorem tr4_exists_sylow_pair (h : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃) {K₄ : Subgroup G}
    (hK₄ : K₄ ∈ twinSet Ω K) (h4K : K₄ ≠ K) (h4K' : K₄ ≠ K') (h4K₃ : K₄ ≠ K₃) :
    ∃ R₃ R₄ : Subgroup G, IsSylow2In R₃ K₃ ∧ IsSylow2In R₄ K₄ ∧
      (∀ r ∈ R₃, u₁ * r = r * u₁) ∧ (∀ r ∈ R₃, u₂ * r = r * u₂) ∧
      (∀ r ∈ R₄, u₁ * r = r * u₁) ∧ (∀ r ∈ R₄, u₂ * r = r * u₂) ∧ Commutes R₃ R₄ := by
  have hΩ : HypOmegaGen Ω := h.hyp
  have hK : K ∈ Ω := h.mem
  have hK' : K' ∈ Ω := h.hK'.1
  have hK₃ : K₃ ∈ Ω := h.hK₃.1
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz := h.hz
  have hz' := h.hzK'
  have hz₃ := h.hzK₃
  have hz₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  have hne : K' ≠ K := h.hne
  have hne₃ : K₃ ≠ K := h.hK₃K
  have hne₃' : K₃ ≠ K' := h.hK₃K'
  set Z₁ := Subgroup.zpowers u₁ with hZ₁
  set Z₂ := Subgroup.zpowers u₂ with hZ₂
  have p₁ : IsPGroup 2 ↥Z₁ := T7A.isPGroup_zpowers_of_orderOf_four h.hu₁.2
  have p₂ : IsPGroup 2 ↥Z₂ := T7A.isPGroup_zpowers_of_orderOf_four h.hu₂.2
  have cm : ∀ {a b : G}, a * b = b * a → Commutes (Subgroup.zpowers a) (Subgroup.zpowers b) := by
    intro a b hab x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute a b from hab) i j).eq
  have c12 : Commutes Z₁ Z₂ := cm h.comm₁₂
  have hP : IsPGroup 2 ↥(Z₁ ⊔ Z₂) :=
    p₁.to_sup_of_normal_right' p₂ (T7A.le_normalizer_of_commutes c12.symm)
  set P := Z₁ ⊔ Z₂ with hPdef
  have hZ₁P : Z₁ ≤ P := le_sup_left
  have hZ₂P : Z₂ ≤ P := le_sup_right
  have hZ₁K : Z₁ ≤ K := Subgroup.zpowers_le.mpr h.hu₁.1
  have hZ₂K' : Z₂ ≤ K' := Subgroup.zpowers_le.mpr h.hu₂.1
  have nK₁ : K ≤ Subgroup.normalizer (K₃ : Set G) :=
    hΩ.le_normalizer_of_twin hK hK₃ hne₃.symm hz hz₃
  have nK₂ : K' ≤ Subgroup.normalizer (K₃ : Set G) :=
    hΩ.le_normalizer_of_twin hK' hK₃ hne₃'.symm hz' hz₃
  have nK₃ : K ≤ Subgroup.normalizer (K₄ : Set G) :=
    hΩ.le_normalizer_of_twin hK hK₄Ω h4K.symm hz hz₄
  have nK₄ : K' ≤ Subgroup.normalizer (K₄ : Set G) :=
    hΩ.le_normalizer_of_twin hK' hK₄Ω h4K'.symm hz' hz₄
  have nK₅ : K₃ ≤ Subgroup.normalizer (K₄ : Set G) :=
    hΩ.le_normalizer_of_twin hK₃ hK₄Ω h4K₃.symm hz₃ hz₄
  have nK₆ : K₄ ≤ Subgroup.normalizer (K₃ : Set G) :=
    hΩ.le_normalizer_of_twin hK₄Ω hK₃ h4K₃ hz₄ hz₃
  have hPK₃ : P ≤ Subgroup.normalizer (K₃ : Set G) :=
    sup_le (hZ₁K.trans nK₁) (hZ₂K'.trans nK₂)
  have hPK₄ : P ≤ Subgroup.normalizer (K₄ : Set G) :=
    sup_le (hZ₁K.trans nK₃) (hZ₂K'.trans nK₄)
  obtain ⟨R₃, hR₃, hR₃fix⟩ := T3.exists_sylow_normalized hP hPK₃
  have hPR₃ : P ≤ Subgroup.normalizer (R₃ : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (hR₃fix x hx)
  have hP₁ : IsPGroup 2 ↥(P ⊔ R₃) := hP.to_sup_of_normal_right' hR₃.2.1 hPR₃
  have hPR₁ : P ⊔ R₃ ≤ Subgroup.normalizer (K₄ : Set G) := sup_le hPK₄ (hR₃.1.trans nK₅)
  obtain ⟨R₄, hR₄, hR₄fix⟩ := T3.exists_sylow_normalized hP₁ hPR₁
  have hPR₄ : P ⊔ R₃ ≤ Subgroup.normalizer (R₄ : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (hR₄fix x hx)
  have hQ : IsPGroup 2 ↥((P ⊔ R₃) ⊔ R₄) := hP₁.to_sup_of_normal_right' hR₄.2.1 hPR₄
  have hZ₁Q : Z₁ ≤ (P ⊔ R₃) ⊔ R₄ := hZ₁P.trans (le_sup_left.trans le_sup_left)
  have hZ₂Q : Z₂ ≤ (P ⊔ R₃) ⊔ R₄ := hZ₂P.trans (le_sup_left.trans le_sup_left)
  have hR₃Q : R₃ ≤ (P ⊔ R₃) ⊔ R₄ := le_sup_right.trans le_sup_left
  have hR₄Q : R₄ ≤ (P ⊔ R₃) ⊔ R₄ := le_sup_right
  have c13 : Commutes Z₁ R₃ := hΩ.commutes_of_twin_of_isPGroup hK hK₃ hne₃.symm hz hz₃ hZ₁K hR₃.1
    (hQ.to_le (sup_le hZ₁Q hR₃Q))
  have c23 : Commutes Z₂ R₃ := hΩ.commutes_of_twin_of_isPGroup hK' hK₃ hne₃'.symm hz' hz₃ hZ₂K' hR₃.1
    (hQ.to_le (sup_le hZ₂Q hR₃Q))
  have c14 : Commutes Z₁ R₄ := hΩ.commutes_of_twin_of_isPGroup hK hK₄Ω h4K.symm hz hz₄ hZ₁K hR₄.1
    (hQ.to_le (sup_le hZ₁Q hR₄Q))
  have c24 : Commutes Z₂ R₄ := hΩ.commutes_of_twin_of_isPGroup hK' hK₄Ω h4K'.symm hz' hz₄ hZ₂K' hR₄.1
    (hQ.to_le (sup_le hZ₂Q hR₄Q))
  have c34 : Commutes R₃ R₄ := hΩ.commutes_of_twin_of_isPGroup hK₃ hK₄Ω h4K₃.symm hz₃ hz₄ hR₃.1 hR₄.1
    (hQ.to_le (sup_le hR₃Q hR₄Q))
  exact ⟨R₃, R₄, hR₃, hR₄, fun r hr => c13 u₁ (Subgroup.mem_zpowers u₁) r hr,
    fun r hr => c23 u₂ (Subgroup.mem_zpowers u₂) r hr,
    fun r hr => c14 u₁ (Subgroup.mem_zpowers u₁) r hr,
    fun r hr => c24 u₂ (Subgroup.mem_zpowers u₂) r hr, c34⟩

end Syl

section Tr3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

@[expose] def SecEdgelessConcl163 (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)),
    Nat.card X < n → TwinDisc.Q8Section X Φ →
      (∀ M ∈ Φ, ∀ N ∈ Φ, ∃ g, conjSub g M = N) → ¬ T3.DStarConnected Φ →
        Disconnected.DEdgeless Φ →
          ∀ L ∈ Φ, ∀ a : X, IsUniqueInvolution L a → ¬ TightInO2 a →
            ∀ P : Subgroup X, IsSylow2In P L →
              ∀ β : MulAut X, β * β = 1 → (∀ x ∈ P, β x = x) → β = 1 ∨ β = MulAut.conj a

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y}

theorem tr3_secFam_dEdgeless (hP : PerpHypS n Y R S t)
    (hd : A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃)
    (hV : ∀ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M = K ∨ M = K' ∨ M = K₃)
    (htrans : ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      ∀ N ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
        ∃ g, conjSub g M = N) :
    Disconnected.DEdgeless (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) := by
  have hΩ := hd.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.sq_12
  have hK₃tq := tq_of_hyp22G hd
  have hΛ : HypOmegaGen (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) :=
    TwinDisc.hypOmegaGen_secFam hΩ hc2
  have key : ∀ N ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      N ∉ omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
        (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) := by
    intro N hN hnb
    obtain ⟨J, hJ, rfl⟩ := exists_of_mem_secFam hN
    exact secImg_not_nbr_of_three hP hd hV hJ hnb
  have key2 : ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      ∀ N ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
        N ∉ omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) M := by
    intro M hM N hN hnb
    obtain ⟨g, hg⟩ := htrans _ (secImg_mem_secFam hK₃tq) M hM
    have h1 := omegaNbr_conj hΛ.conjInvariant hnb g⁻¹
    rw [← hg, conjSub_inv_conjSub] at h1
    exact key _ (hΛ.conjInvariant g⁻¹ N hN) h1
  intro M hM N hN hadj
  rcases hadj with h | h
  · exact key2 M hM N hN h
  · exact key2 N hN M hM h

theorem v3AbelianO2TrS3_of_edgeless {n : ℕ} (hSec : SecEdgelessConcl163 n) : V3AbelianO2TrS3 n := by
  classical
  intro Y _ _ R S t hP h3 hE K K' K₃ u₁ u₂ u₃ d hV W hW hconnW htC htH htrans hconn
  have hΩ := d.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one d.sq_12
  have hK₃tq := tq_of_hyp22G d
  have hS := layer_q8Section hP d.sq_12
  have hlt := card_layer_lt hP d.mul_ne_one
  have hex : ∀ J ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      ∃ u' : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) ⧸
        classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
      IsUniqueInvolution (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) J) u' := by
    intro J hJ
    obtain ⟨⟨z, hz⟩, -⟩ := hS.hyp.omega1 _ (secImg_mem_secFam hJ)
    exact ⟨z, hz⟩
  have hedge := tr3_secFam_dEdgeless hP d hV htrans
  set tb : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) ⧸
      classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) :=
    QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))
      (⟨⟨t, htC⟩, htH⟩ : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) with htbdef
  have htb₃ : IsUniqueInvolution (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) tb :=
    isUniqueInvolution_secImg_mk hK₃tq (hex K₃ hK₃tq) d.hzK₃ htC
  by_contra hno
  obtain ⟨R₁, R₂, R₃, hR₁, hR₂, hR₃, hu₁R, hu₂R, -, c12, c13, c23⟩ := tr3_exists_sylow_triple d
  obtain ⟨e₁⟩ := members_sylow_q8 hP K d.mem R₁ hR₁
  obtain ⟨e₂⟩ := members_sylow_q8 hP K' d.hK'.1 R₂ hR₂
  obtain ⟨w₁, hw₁R, hw₁sq, hw₁u⟩ := tr3_exists_inverting e₁ hu₁R d.sq₁ d.hz.sq d.hz.ne_one
  obtain ⟨w₂, hw₂R, hw₂sq, hw₂u⟩ := tr3_exists_inverting e₂ hu₂R d.sq₂ d.hz.sq d.hz.ne_one
  have h1w₂ : u₁ * w₂ = w₂ * u₁ := c12 u₁ hu₁R w₂ hw₂R
  have h2w₁ : u₂ * w₁ = w₁ * u₂ := (c12 w₁ hw₁R u₂ hu₂R).symm
  have hww : w₁ * w₂ = w₂ * w₁ := c12 w₁ hw₁R w₂ hw₂R
  obtain ⟨hv2, hvu, hvc⟩ := tr3_kk_device d.hz.sq d.sq₁ d.sq₂ hw₁sq hw₂sq hw₁u hw₂u h1w₂ h2w₁ hww
  have hvC : w₁ * w₂ ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hvu.symm
  have hu₁C : u₁ ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc u₁ * (u₁ * u₂) = u₁ * (u₂ * u₁) := by rw [d.comm₁₂]
      _ = (u₁ * u₂) * u₁ := by group
  have hbb : secAct hΩ hc2 ⟨w₁ * w₂, hvC⟩ * secAct hΩ hc2 ⟨w₁ * w₂, hvC⟩ = 1 := by
    have h := congrArg (secAct hΩ hc2) (show (⟨w₁ * w₂, hvC⟩ * ⟨w₁ * w₂, hvC⟩ :
      ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) = 1 from Subtype.ext hv2)
    simpa only [map_mul, map_one] using h
  have haa : secAct hΩ hc2 ⟨u₁, hu₁C⟩ * secAct hΩ hc2 ⟨u₁, hu₁C⟩ = secAct hΩ hc2 ⟨t, htC⟩ := by
    have h := congrArg (secAct hΩ hc2) (show (⟨u₁, hu₁C⟩ * ⟨u₁, hu₁C⟩ :
      ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) = ⟨t, htC⟩ from Subtype.ext d.sq₁)
    simpa only [map_mul] using h
  have hab : secAct hΩ hc2 ⟨u₁, hu₁C⟩ * secAct hΩ hc2 ⟨w₁ * w₂, hvC⟩ * (secAct hΩ hc2 ⟨u₁, hu₁C⟩)⁻¹ *
      (secAct hΩ hc2 ⟨w₁ * w₂, hvC⟩)⁻¹ = secAct hΩ hc2 ⟨t, htC⟩ := by
    have h := congrArg (secAct hΩ hc2) (show (⟨u₁, hu₁C⟩ * ⟨w₁ * w₂, hvC⟩ * ⟨u₁, hu₁C⟩⁻¹ *
      ⟨w₁ * w₂, hvC⟩⁻¹ : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) = ⟨t, htC⟩ from
        Subtype.ext hvc)
    simpa only [map_mul, map_inv] using h
  have hat : secAct hΩ hc2 ⟨t, htC⟩ = MulAut.conj tb := secAct_of_mem hΩ hc2 htH
  have hR₃c : R₃ ≤ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
    intro r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : u₁ * r = r * u₁ := c13 u₁ hu₁R r hr
    have h2 : u₂ * r = r * u₂ := c23 u₂ hu₂R r hr
    calc r * (u₁ * u₂) = (r * u₁) * u₂ := by group
      _ = (u₁ * r) * u₂ := by rw [h1]
      _ = u₁ * (r * u₂) := by group
      _ = u₁ * (u₂ * r) := by rw [h2]
      _ = (u₁ * u₂) * r := by group
  have hvR₃ : ∀ r ∈ R₃, (w₁ * w₂) * r = r * (w₁ * w₂) := by
    intro r hr
    have h1 : w₁ * r = r * w₁ := c13 w₁ hw₁R r hr
    have h2 : w₂ * r = r * w₂ := c23 w₂ hw₂R r hr
    calc (w₁ * w₂) * r = w₁ * (w₂ * r) := by group
      _ = w₁ * (r * w₂) := by rw [h2]
      _ = (w₁ * r) * w₂ := by group
      _ = (r * w₁) * w₂ := by rw [h1]
      _ = r * (w₁ * w₂) := by group
  have hs1 := (((TwinADescent.isSylow2In_coreAt_iff hc2 hK₃tq.2).mpr ⟨hR₃, hR₃c⟩).subgroupOf
    (TwinADescent.coreAt_le_centralizer (u₁ * u₂) K₃))
  have hs2 := hs1.subgroupOf (le_coreHull hK₃tq)
  have hs3 := isSylow2In_map_mk (CFSG.ComponentClassification.OddCore.odd_card
    ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) hs2
  have hfix : ∀ x ∈ ((R₃.subgroupOf (Subgroup.centralizer ({u₁ * u₂} : Set Y))).subgroupOf
      (coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))).map
        (QuotientGroup.mk' (classicalInvolutionOddCore
          ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))),
      secAct hΩ hc2 ⟨w₁ * w₂, hvC⟩ x = x := by
    rintro _ ⟨y, hy, rfl⟩
    show secAct hΩ hc2 ⟨w₁ * w₂, hvC⟩ (QuotientGroup.mk y) = QuotientGroup.mk y
    rw [secAct_mk]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    have hyR : (((y : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y)) ∈ R₃ := hy
    have := hvR₃ _ hyR
    show (w₁ * w₂) * (((y : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y)) * (w₁ * w₂)⁻¹ =
      (((y : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y))
    rw [this]
    group
  have hres := hSec _ (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) hlt hS
    htrans hconn hedge _ (secImg_mem_secFam hK₃tq) tb htb₃ hno _ hs3
    (secAct hΩ hc2 ⟨w₁ * w₂, hvC⟩) hbb hfix
  have hcomm : secAct hΩ hc2 ⟨u₁, hu₁C⟩ * secAct hΩ hc2 ⟨w₁ * w₂, hvC⟩ * (secAct hΩ hc2 ⟨u₁, hu₁C⟩)⁻¹ *
      (secAct hΩ hc2 ⟨w₁ * w₂, hvC⟩)⁻¹ = 1 := by
    rcases hres with h1 | h1
    · rw [h1]
      group
    · have h2 : secAct hΩ hc2 ⟨w₁ * w₂, hvC⟩ =
          secAct hΩ hc2 ⟨u₁, hu₁C⟩ * secAct hΩ hc2 ⟨u₁, hu₁C⟩ := by
        rw [h1, haa, hat]
      rw [h2]
      group
  have h1 : MulAut.conj tb = 1 := by rw [← hat, ← hab, hcomm]
  have hcent : ∀ y, y * tb = tb * y := by
    intro y
    have h2 := congrArg (fun f => f y) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    have h2' : tb * y * tb⁻¹ = y := h2
    calc y * tb = (tb * y * tb⁻¹) * tb := by rw [h2']
      _ = tb * y := by group
  exact hno (tightInO2_of_central htb₃.sq hcent)

@[expose] def SecTwinNoRoot (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → ∀ Φ : Set (Subgroup X),
    TwinDisc.Q8Section X Φ → (∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) →
      ¬ T3.DStarConnected Φ → TwinDisc.NoExit X Φ →
        ∀ A ∈ Φ, ∀ B ∈ omegaNbr Φ A, ∀ x : X, IsUniqueInvolution A x → IsUniqueInvolution B x →
          ∀ α : MulAut X, (∀ a ∈ A, α a = a) → (∀ b ∈ B, α b = b) → α * α ≠ MulAut.conj x

theorem v3AbelianO2TrG4_of_noRoot {n : ℕ} (hmodel : TwinDisc.ExitE4.E4ModelDStar)
    (hPb : TL4.TightBelowRPlus 3 n) (hcit : CIT3Below n) (hOE : TwinDisc.OddCentEdge n)
    (hSec : SecTwinNoRoot n) : V3AbelianO2TrG4 n := by
  classical
  intro Y _ _ R S t hP h3 hE K K' K₃ u₁ u₂ u₃ d hV W hW hconnW htC htH htrans hconn
  have hΩ := d.hyp
  obtain ⟨K₄, hK₄, h4K, h4K', h4K₃⟩ : ∃ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K,
      M ≠ K ∧ M ≠ K' ∧ M ≠ K₃ := by
    by_contra hcon
    apply hV
    intro M hM
    by_contra hM'
    push Not at hM'
    exact hcon ⟨M, hM, hM'.1, hM'.2.1, hM'.2.2⟩
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one d.sq_12
  have hK₃tq := tq_of_hyp22G d
  have hz₄ : IsUniqueInvolution K₄ t := isUniqueInvolution_of_mem_twinSet d.hz hK₄
  have hu₁₃ : u₁ ∈ trivialOnQuot K₃ :=
    A7T22.le_trivialOnQuot_of_twin hΩ d.mem d.hK₃.1 d.hK₃K.symm d.hz d.hzK₃ d.hu₁.1
  have hu₁₄ : u₁ ∈ trivialOnQuot K₄ :=
    A7T22.le_trivialOnQuot_of_twin hΩ d.mem hK₄.1 h4K.symm d.hz hz₄ d.hu₁.1
  have hu₂₄ : u₂ ∈ trivialOnQuot K₄ :=
    A7T22.le_trivialOnQuot_of_twin hΩ d.hK'.1 hK₄.1 h4K'.symm d.hzK' hz₄ d.hu₂.1
  have hK₄tq : K₄ ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) :=
    ⟨hK₄.1, Subgroup.mul_mem _ hu₁₄ hu₂₄⟩
  have hS := layer_q8Section hP d.sq_12
  have hlt := card_layer_lt hP d.mul_ne_one
  have hex : ∀ J ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      ∃ u' : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) ⧸
        classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
      IsUniqueInvolution (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) J) u' := by
    intro J hJ
    obtain ⟨⟨z, hz⟩, -⟩ := hS.hyp.omega1 _ (secImg_mem_secFam hJ)
    exact ⟨z, hz⟩
  set tb : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) ⧸
      classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) :=
    QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))
      (⟨⟨t, htC⟩, htH⟩ : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) with htbdef
  have htb₃ : IsUniqueInvolution (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) tb :=
    isUniqueInvolution_secImg_mk hK₃tq (hex K₃ hK₃tq) d.hzK₃ htC
  have htb₄ : IsUniqueInvolution (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄) tb :=
    isUniqueInvolution_secImg_mk hK₄tq (hex K₄ hK₄tq) hz₄ htC
  obtain ⟨R₃, R₄, hR₃, hR₄, h13, h23, h14, h24, c34⟩ := tr4_exists_sylow_pair d hK₄ h4K h4K' h4K₃
  have hcentr : ∀ {Q : Subgroup Y}, (∀ r ∈ Q, u₁ * r = r * u₁) → (∀ r ∈ Q, u₂ * r = r * u₂) →
      Q ≤ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
    intro Q h1 h2 r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 := h1 r hr
    have e2 := h2 r hr
    calc r * (u₁ * u₂) = (r * u₁) * u₂ := by group
      _ = (u₁ * r) * u₂ := by rw [← e1]
      _ = u₁ * (r * u₂) := by group
      _ = u₁ * (u₂ * r) := by rw [← e2]
      _ = (u₁ * u₂) * r := by group
  have hnb : secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄ ∈
      omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
        (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) :=
    omegaNbr_secImg hΩ hc2 hK₃tq hK₄tq hR₃ hR₄ (hcentr h13 h23) (hcentr h14 h24) c34
      (hR₄.1.trans (hΩ.le_normalizer_of_twin hK₄.1 d.hK₃.1 h4K₃ hz₄ d.hzK₃))
  have hedge : ∃ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      ∃ N : Subgroup (↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) ⧸
        classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))),
        N ∈ omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) M :=
    ⟨_, secImg_mem_secFam hK₃tq, _, hnb⟩
  have hodd := fun M (hM : M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
      (z : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) ⧸
        classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))
      (hz : IsUniqueInvolution M z) =>
    hOE hcit hPb _ hlt _ hS htrans hedge M hM z hz
  rcases TwinDisc.ExitU.noExit_or_ae5 hmodel hPb.thmD.d2 hlt hS htrans hedge hodd hconn with
    hNo | ⟨⟨M, hM, z, hz, hO⟩, -⟩
  ·
    exfalso
    have h2 := (TwinDisc.lifts_of_noExit hPb hlt hS hNo).1
    have hu₁C : u₁ ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc u₁ * (u₁ * u₂) = u₁ * (u₂ * u₁) := by rw [d.comm₁₂]
        _ = (u₁ * u₂) * u₁ := by group
    have hfix₃ := secAct_fix_secImg hΩ hc2 (h2 _ (secImg_mem_secFam hK₃tq)) hu₁C hu₁₃
    have hfix₄ := secAct_fix_secImg hΩ hc2 (h2 _ (secImg_mem_secFam hK₄tq)) hu₁C hu₁₄
    have haa : secAct hΩ hc2 ⟨u₁, hu₁C⟩ * secAct hΩ hc2 ⟨u₁, hu₁C⟩ = secAct hΩ hc2 ⟨t, htC⟩ := by
      have h := congrArg (secAct hΩ hc2) (show (⟨u₁, hu₁C⟩ * ⟨u₁, hu₁C⟩ :
        ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) = ⟨t, htC⟩ from Subtype.ext d.sq₁)
      simpa only [map_mul] using h
    have hat : secAct hΩ hc2 ⟨t, htC⟩ = MulAut.conj tb := secAct_of_mem hΩ hc2 htH
    exact hSec _ hlt _ hS htrans hconn hNo _ (secImg_mem_secFam hK₃tq) _ hnb tb htb₃ htb₄
      (secAct hΩ hc2 ⟨u₁, hu₁C⟩) hfix₃ hfix₄ (haa.trans hat)
  ·
    obtain ⟨g, hg⟩ := htrans M hM _ (secImg_mem_secFam hK₃tq)
    have h1 : IsUniqueInvolution (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃)
        (g * z * g⁻¹) := hg ▸ hz.conj g
    rw [← h1.eq htb₃]
    exact TL4.tightInO2_conj hO g

theorem v3AbelianO2TrG4_of_noRoot'
    {n : ℕ} (hPb : TL4.TightBelowRPlus 3 n) (hcit : CIT3Below n)
    (hSec : SecTwinNoRoot n) : V3AbelianO2TrG4 n :=
  v3AbelianO2TrG4_of_noRoot TwinDisc.ExitE4.e4ModelDStar_of_certs hPb hcit
    (TwinDisc.oddCentEdge_proved n) hSec

end Tr3

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
