module

public import CFSG.RankThree.PartOne.KC.LinearPlaneGeneration

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis

open Module CFSG.RankThree.PartOne.KCLinPlane

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def IsTv (G : Subgroup (V ≃ₗ[K] V)) (w : V) (φ : Module.Dual K V) : Prop :=
  φ w = 0 ∧ ∃ u ∈ G, ∀ v, u v = v + φ v • w

theorem IsTv.mul_dir {G : Subgroup (V ≃ₗ[K] V)} {w w' : V} {φ : Module.Dual K V}
    (h : IsTv G w φ) (h' : IsTv G w' φ) : IsTv G (w + w') φ := by
  obtain ⟨hw, u, hu, huv⟩ := h
  obtain ⟨hw', u', hu', hu'v⟩ := h'
  refine ⟨by rw [map_add, hw, hw', add_zero], u * u', G.mul_mem hu hu', fun v => ?_⟩
  change u (u' v) = _
  rw [hu'v, map_add, map_smul, huv, huv, hw']
  module

theorem IsTv.mul_fun {G : Subgroup (V ≃ₗ[K] V)} {w : V} {φ φ' : Module.Dual K V}
    (h : IsTv G w φ) (h' : IsTv G w φ') : IsTv G w (φ + φ') := by
  obtain ⟨hw, u, hu, huv⟩ := h
  obtain ⟨hw', u', hu', hu'v⟩ := h'
  refine ⟨by simp [hw, hw'], u * u', G.mul_mem hu hu', fun v => ?_⟩
  change u (u' v) = _
  rw [hu'v, map_add, map_smul, huv, huv, hw]
  simp only [LinearMap.add_apply]
  module

theorem IsTv.inv_apply {w : V} {φ : Module.Dual K V}
    {u : V ≃ₗ[K] V} (hw : φ w = 0) (huv : ∀ v, u v = v + φ v • w) (v : V) :
    u⁻¹ v = v - φ v • w := by
  have h1 : u (u⁻¹ v) = v := by
    change u (u.symm v) = v
    exact u.apply_symm_apply v
  have h2 := huv (u⁻¹ v)
  rw [h1] at h2
  have h3 : φ (u⁻¹ v) = φ v := by
    have := congrArg φ h2
    rw [map_add, map_smul, hw] at this
    simpa using this.symm
  rw [h3] at h2
  exact eq_sub_of_add_eq h2.symm

theorem IsTv.neg_dir {G : Subgroup (V ≃ₗ[K] V)} {w : V} {φ : Module.Dual K V}
    (h : IsTv G w φ) : IsTv G (-w) φ := by
  obtain ⟨hw, u, hu, huv⟩ := h
  refine ⟨by rw [map_neg, hw, neg_zero], u⁻¹, G.inv_mem hu, fun v => ?_⟩
  rw [IsTv.inv_apply hw huv]
  module

theorem IsTv.neg_fun {G : Subgroup (V ≃ₗ[K] V)} {w : V} {φ : Module.Dual K V}
    (h : IsTv G w φ) : IsTv G w (-φ) := by
  obtain ⟨hw, u, hu, huv⟩ := h
  refine ⟨by simp [hw], u⁻¹, G.inv_mem hu, fun v => ?_⟩
  rw [IsTv.inv_apply hw huv]
  simp only [LinearMap.neg_apply]
  module

theorem IsTv.conj {G : Subgroup (V ≃ₗ[K] V)} {w : V} {φ : Module.Dual K V}
    (h : IsTv G w φ) {g : V ≃ₗ[K] V} (hg : g ∈ G) :
    IsTv G (g w) (φ.comp (g.symm : V →ₗ[K] V)) := by
  obtain ⟨hw, u, hu, huv⟩ := h
  refine ⟨by simpa using hw, g * u * g⁻¹, G.mul_mem (G.mul_mem hg hu) (G.inv_mem hg),
    fun v => ?_⟩
  change g (u (g.symm v)) = _
  rw [huv, map_add, map_smul]
  simp

theorem transvection_mem_suppGroup' {f : Module.End K V} {a : V} (ha : f a = a)
    {l : Module.Dual K V} (hl : ∀ v, l (f v) = l v) (hla : l a = 0) :
    LinearEquiv.transvection hla ∈ suppGroup f := by
  refine ⟨?_, fun v => ?_, fun v => ?_⟩
  · exact LinearEquiv.transvection.det_eq_one hla
  · change (LinearEquiv.transvection hla) (f v) = f ((LinearEquiv.transvection hla) v)
    change f v + l (f v) • a = f (v + l v • a)
    rw [map_add, map_smul, ha, hl]
  · change (v - f v) + l (v - f v) • a = v - f v
    rw [map_sub, hl]
    simp

theorem isTv_suppGroup {f : Module.End K V} {a : V} (ha : f a = a)
    {l : Module.Dual K V} (hl : ∀ v, l (f v) = l v) (hla : l a = 0) :
    IsTv (suppGroup f) a l :=
  ⟨hla, LinearEquiv.transvection hla, transvection_mem_suppGroup' ha hl hla, fun v => rfl⟩

theorem transvection_symm_apply' {a : V} {l : Module.Dual K V} (hla : l a = 0) (v : V) :
    (LinearEquiv.transvection hla).symm v = v - l v • a := by
  rw [LinearEquiv.symm_apply_eq]
  change v = (v - l v • a) + l (v - l v • a) • a
  rw [map_sub, map_smul, hla]
  simp

theorem IsTv.peel_fun {G : Subgroup (V ≃ₗ[K] V)} {f : Module.End K V}
    (hG : suppGroup f ≤ G) {w : V} {φ : Module.Dual K V}
    (h : IsTv G w φ) (hw : f w = 0) {a : V} (ha : f a = a) {l : Module.Dual K V}
    (hl : ∀ v, l (f v) = l v) (hla : l a = 0) : IsTv G w ((φ a) • l) := by
  have hT : (LinearEquiv.transvection hla) ∈ G := hG (transvection_mem_suppGroup' ha hl hla)
  have hlw : l w = 0 := by rw [← hl w, hw, map_zero]
  have h1 := h.conj hT
  have e1 : (LinearEquiv.transvection hla) w = w := by
    change w + l w • a = w
    rw [hlw]; simp
  rw [e1] at h1
  have e2 : φ.comp ((LinearEquiv.transvection hla).symm : V →ₗ[K] V) = φ - (φ a) • l := by
    ext v
    simp [transvection_symm_apply' hla, sub_eq_add_neg, smul_eq_mul, mul_comm]
  rw [e2] at h1
  have h2 := (h.neg_fun).mul_fun h1
  have e3 : -φ + (φ - (φ a) • l) = -((φ a) • l) := by abel
  rw [e3] at h2
  have := h2.neg_fun
  rwa [neg_neg] at this

theorem IsTv.peel_dir {G : Subgroup (V ≃ₗ[K] V)} {f : Module.End K V}
    (hG : suppGroup f ≤ G) {w : V} {φ : Module.Dual K V}
    (h : IsTv G w φ) (hφ : ∀ v, φ (f v) = 0) {a : V} (ha : f a = a) {l : Module.Dual K V}
    (hl : ∀ v, l (f v) = l v) (hla : l a = 0) : IsTv G ((l w) • a) φ := by
  have hT : (LinearEquiv.transvection hla) ∈ G := hG (transvection_mem_suppGroup' ha hl hla)
  have h1 := h.conj hT
  have hφa : φ a = 0 := by rw [← ha, hφ]
  have e2 : φ.comp ((LinearEquiv.transvection hla).symm : V →ₗ[K] V) = φ := by
    ext v
    simp [transvection_symm_apply' hla, hφa]
  rw [e2] at h1
  have h2 := h1.mul_dir h.neg_dir
  have e3 : (LinearEquiv.transvection hla) w + -w = (l w) • a := by
    change w + l w • a + -w = _
    abel
  rwa [e3] at h2

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis
