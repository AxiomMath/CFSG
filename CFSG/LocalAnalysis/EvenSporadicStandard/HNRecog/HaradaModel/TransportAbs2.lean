module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.TransportAbs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.EichlerDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongr

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA
open CFSG.EvenSporadicStandard.HNRecog.TwoHSData

variable {H K : Type} [Group H] [Group K]

theorem map_le_centralizer_singleton (e : H ≃* K) {R : Subgroup H} {z : H}
    (h : R ≤ centralizer ({z} : Set H)) : R.map e.toMonoidHom ≤ centralizer ({e z} : Set K) := by
  calc R.map e.toMonoidHom ≤ (centralizer ({z} : Set H)).map e.toMonoidHom :=
        Subgroup.map_mono h
    _ = centralizer ({e z} : Set K) := map_centralizer_singleton e z

theorem map_le_normalizer_range (e : H ≃* K) (ι : Elem2 6 →* H) {R : Subgroup H}
    (h : R ≤ normalizer (ι.range : Set H)) :
    R.map e.toMonoidHom ≤ normalizer ((e.toMonoidHom.comp ι).range : Set K) := by
  calc R.map e.toMonoidHom ≤ (normalizer (ι.range : Set H)).map e.toMonoidHom :=
        Subgroup.map_mono h
    _ ≤ normalizer ((ι.range.map e.toMonoidHom : Subgroup K) : Set K) :=
        Subgroup.le_normalizer_map (H := ι.range) e.toMonoidHom
    _ = normalizer (((e.toMonoidHom.comp ι).range : Subgroup K) : Set K) := by
        rw [range_comp_mulEquiv]

theorem normal_map (e : H ≃* K) {C R : Subgroup H}
    (h : ∀ c ∈ C, ∀ x ∈ R, c * x * c⁻¹ ∈ R) :
    ∀ c ∈ C.map e.toMonoidHom, ∀ x ∈ R.map e.toMonoidHom, c * x * c⁻¹ ∈ R.map e.toMonoidHom := by
  intro c hc x hx
  obtain ⟨c0, hc0, rfl⟩ := Subgroup.mem_map.mp hc
  obtain ⟨x0, hx0, rfl⟩ := Subgroup.mem_map.mp hx
  exact Subgroup.mem_map.mpr
    ⟨c0 * x0 * c0⁻¹, h c0 hc0 x0 hx0, by simp only [map_mul, map_inv]⟩

theorem max_map (e : H ≃* K) {C R : Subgroup H}
    (h : ∀ P : Subgroup H, P ≤ C → IsPGroup 2 ↥P → (∀ c ∈ C, ∀ x ∈ P, c * x * c⁻¹ ∈ P) →
      P ≤ R) :
    ∀ P : Subgroup K, P ≤ C.map e.toMonoidHom → IsPGroup 2 ↥P →
      (∀ c ∈ C.map e.toMonoidHom, ∀ x ∈ P, c * x * c⁻¹ ∈ P) → P ≤ R.map e.toMonoidHom := by
  intro P hPC hPgrp hPnorm
  let P0 : Subgroup H := P.comap e.toMonoidHom
  have hP0C : P0 ≤ C := fun y hy => (mem_map_iff e C y).mp (hPC hy)
  have hP0grp : IsPGroup 2 ↥P0 := hPgrp.comap_of_injective e.toMonoidHom e.injective
  have hP0norm : ∀ c ∈ C, ∀ x ∈ P0, c * x * c⁻¹ ∈ P0 := by
    intro c hc x hx
    rw [Subgroup.mem_comap]
    have h1 : e.toMonoidHom c ∈ C.map e.toMonoidHom := Subgroup.mem_map.mpr ⟨c, hc, rfl⟩
    have h2 : e.toMonoidHom x ∈ P := hx
    have h3 := hPnorm (e.toMonoidHom c) h1 (e.toMonoidHom x) h2
    simpa only [map_mul, map_inv] using h3
  have hP0R : P0 ≤ R := h P0 hP0C hP0grp hP0norm
  intro y hy
  refine Subgroup.mem_map.mpr ⟨e.symm y, hP0R ?_, e.apply_symm_apply y⟩
  show e.symm y ∈ P.comap e.toMonoidHom
  rw [Subgroup.mem_comap]
  simpa only [MulEquiv.coe_toMonoidHom, e.apply_symm_apply] using hy

theorem sq_map (e : H ≃* K) {R : Subgroup H} {z : H}
    (h : ∀ x ∈ R, x ^ 2 ∈ zpowers z) : ∀ x ∈ R.map e.toMonoidHom, x ^ 2 ∈ zpowers (e z) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  rw [← map_pow]
  have hm : e.toMonoidHom (y ^ 2) ∈ (Subgroup.zpowers z).map e.toMonoidHom :=
    Subgroup.mem_map.mpr ⟨y ^ 2, h y hy, rfl⟩
  simpa only [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom] using hm

theorem comm_map (e : H ≃* K) {R : Subgroup H} {z : H}
    (h : ∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ zpowers z) :
    ∀ x ∈ R.map e.toMonoidHom, ∀ y ∈ R.map e.toMonoidHom,
      x * y * x⁻¹ * y⁻¹ ∈ zpowers (e z) := by
  intro x hx y hy
  obtain ⟨x0, hx0, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨y0, hy0, rfl⟩ := Subgroup.mem_map.mp hy
  rw [show e.toMonoidHom x0 * e.toMonoidHom y0 * (e.toMonoidHom x0)⁻¹ * (e.toMonoidHom y0)⁻¹
        = e.toMonoidHom (x0 * y0 * x0⁻¹ * y0⁻¹) by simp only [map_mul, map_inv]]
  have hm : e.toMonoidHom (x0 * y0 * x0⁻¹ * y0⁻¹) ∈ (Subgroup.zpowers z).map e.toMonoidHom :=
    Subgroup.mem_map.mpr ⟨_, h x0 hx0 y0 hy0, rfl⟩
  simpa only [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom] using hm

theorem faith_map (e : H ≃* K) {C R : Subgroup H} {z : H}
    (h : ∀ c ∈ C, (∀ x ∈ R, c * x * c⁻¹ * x⁻¹ ∈ zpowers z) → c ∈ R) :
    ∀ c ∈ C.map e.toMonoidHom, (∀ x ∈ R.map e.toMonoidHom, c * x * c⁻¹ * x⁻¹ ∈ zpowers (e z)) →
      c ∈ R.map e.toMonoidHom := by
  intro c hc htriv
  obtain ⟨c0, hc0, rfl⟩ := Subgroup.mem_map.mp hc
  refine Subgroup.mem_map.mpr ⟨c0, h c0 hc0 ?_, rfl⟩
  intro x hx
  have hmem : e.toMonoidHom (c0 * x * c0⁻¹ * x⁻¹) ∈ zpowers (e z) := by
    have hxmap : e.toMonoidHom x ∈ R.map e.toMonoidHom := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have h3 := htriv (e.toMonoidHom x) hxmap
    simpa only [map_mul, map_inv] using h3
  exact (mem_map_iff e (Subgroup.zpowers z) (c0 * x * c0⁻¹ * x⁻¹)).mp
    (by simpa only [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom] using hmem)

theorem eichler_map (e : H ≃* K) (ι : Elem2 6 →* H) {R : Subgroup H} {zv : V6}
    (h : ∀ r ∈ R, ∃ u : V6, bil u zv = 0 ∧ lam u = 0 ∧
      ∀ x : V6, r * ι (Multiplicative.ofAdd x) * r⁻¹ = ι (Multiplicative.ofAdd (eichF zv u x))) :
    ∀ r ∈ R.map e.toMonoidHom, ∃ u : V6, bil u zv = 0 ∧ lam u = 0 ∧
      ∀ x : V6, r * (e.toMonoidHom.comp ι) (Multiplicative.ofAdd x) * r⁻¹ =
        (e.toMonoidHom.comp ι) (Multiplicative.ofAdd (eichF zv u x)) := by
  intro r hr
  obtain ⟨r0, hr0, rfl⟩ := Subgroup.mem_map.mp hr
  obtain ⟨u, hu1, hu2, hu3⟩ := h r0 hr0
  refine ⟨u, hu1, hu2, ?_⟩
  intro x
  simp only [MonoidHom.comp_apply]
  rw [show e.toMonoidHom r0 * e.toMonoidHom (ι (Multiplicative.ofAdd x)) * (e.toMonoidHom r0)⁻¹
        = e.toMonoidHom (r0 * ι (Multiplicative.ofAdd x) * r0⁻¹) by simp only [map_mul, map_inv],
      hu3 x]

theorem surj_map (e : H ≃* K) (ι : Elem2 6 →* H) {R : Subgroup H} {zv : V6}
    (h : ∀ u : V6, bil u zv = 0 → lam u = 0 → ∃ r ∈ R,
      ∀ x : V6, r * ι (Multiplicative.ofAdd x) * r⁻¹ = ι (Multiplicative.ofAdd (eichF zv u x))) :
    ∀ u : V6, bil u zv = 0 → lam u = 0 → ∃ r ∈ R.map e.toMonoidHom,
      ∀ x : V6, r * (e.toMonoidHom.comp ι) (Multiplicative.ofAdd x) * r⁻¹ =
        (e.toMonoidHom.comp ι) (Multiplicative.ofAdd (eichF zv u x)) := by
  intro u hu1 hu2
  obtain ⟨r0, hr0, hr⟩ := h u hu1 hu2
  refine ⟨e.toMonoidHom r0, Subgroup.mem_map.mpr ⟨r0, hr0, rfl⟩, ?_⟩
  intro x
  simp only [MonoidHom.comp_apply]
  rw [show e.toMonoidHom r0 * e.toMonoidHom (ι (Multiplicative.ofAdd x)) * (e.toMonoidHom r0)⁻¹
        = e.toMonoidHom (r0 * ι (Multiplicative.ofAdd x) * r0⁻¹) by simp only [map_mul, map_inv],
      hr x]

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
