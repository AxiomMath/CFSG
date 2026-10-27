module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.S25

open Subgroup

@[expose] def SplusFact {H : Type*} [Group H] (z : H) : Prop :=
  ∀ Y : Subgroup H, Y ≤ centralizer ({z} : Set H) → ⁅Y, Y⁆ = Y →
    ∀ f : ↥Y →* alternatingGroup (Fin 5), Function.Surjective f →
      f.ker ≤ (zpowers z).subgroupOf Y → False

theorem SplusFact.map_injective {H G : Type*} [Group H] [Group G] {z : H} (h : SplusFact z)
    (φ : H →* G) (hφ : Function.Injective φ) :
    ∀ Y : Subgroup G, Y ≤ φ.range → Y ≤ centralizer ({φ z} : Set G) → ⁅Y, Y⁆ = Y →
      ∀ f : ↥Y →* alternatingGroup (Fin 5), Function.Surjective f →
        f.ker ≤ (zpowers (φ z)).subgroupOf Y → False := by
  intro Y hYrange hYc hperf f hf hfk
  let Y0 : Subgroup H := Y.comap φ
  have hmap : Y0.map φ = Y := Subgroup.map_comap_eq_self hYrange
  let e : ↥Y0 ≃* ↥Y :=
    (Subgroup.equivMapOfInjective Y0 φ hφ).trans (MulEquiv.subgroupCongr hmap)
  have he_coe : ∀ x : ↥Y0, (e x : G) = φ x := by
    intro x
    simp [e]
  have hY0c : Y0 ≤ centralizer ({z} : Set H) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyY : φ y ∈ Y := hy
    have hcomm : φ y * φ z = φ z * φ y :=
      Subgroup.mem_centralizer_singleton_iff.mp (hYc hyY)
    exact hφ (by rw [map_mul, map_mul, hcomm])
  have hY0perf : ⁅Y0, Y0⁆ = Y0 := by
    apply Subgroup.map_injective hφ
    rw [Subgroup.map_commutator, hmap, hperf]
  let f0 : ↥Y0 →* alternatingGroup (Fin 5) := f.comp e.toMonoidHom
  have hf0 : Function.Surjective f0 := hf.comp e.surjective
  have hf0k : f0.ker ≤ (zpowers z).subgroupOf Y0 := by
    intro x hx
    have hxzp : φ x ∈ (zpowers z).map φ := by
      rw [MonoidHom.map_zpowers]
      have hxmem : (e x : G) ∈ zpowers (φ z) := Subgroup.mem_subgroupOf.mp (hfk hx)
      rwa [he_coe x] at hxmem
    exact Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_map_iff_mem hφ).mp hxzp)
  exact h Y0 hY0c hY0perf f0 hf0 hf0k

theorem SplusFact.of_mulEquiv {H K : Type*} [Group H] [Group K] {z : H} (h : SplusFact z)
    (e : H ≃* K) : SplusFact (e z) := fun Y hYc hperf f hf hfk =>
  h.map_injective e.toMonoidHom e.injective Y
    (by rw [show e.toMonoidHom.range = ⊤ from e.toMonoidHom.range_eq_top_of_surjective e.surjective]
        exact le_top)
    hYc hperf f hf hfk

end CFSG.EvenSporadicStandard.HNRecog.Harada.S25
