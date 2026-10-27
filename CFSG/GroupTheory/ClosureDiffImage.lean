module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.End

public section

namespace CFSG.GroupTheory

theorem mem_closure_image_diff_iff {H K : Type*} [Group H] [Group K] {f : H →* K}
    (hf : Function.Injective f) {S : Set H} {x : H} :
    f x ∈ Subgroup.closure (f '' S \ {f x}) ↔ x ∈ Subgroup.closure (S \ {x}) := by
  rw [← Set.image_singleton, ← Set.image_diff hf, ← MonoidHom.map_closure,
    Subgroup.mem_map_iff_mem hf]

theorem mem_closure_preimage_diff_of_injective {H K : Type*} [Group H] [Group K] {f : H →* K}
    (hf : Function.Injective f) {Λ : Set K} (hΛ : Λ ⊆ Set.range f) {x : H}
    (hx : f x ∈ Subgroup.closure (Λ \ {f x})) :
    x ∈ Subgroup.closure (f ⁻¹' Λ \ {x}) := by
  rwa [← mem_closure_image_diff_iff hf, Set.image_preimage_eq_of_subset hΛ]

theorem conj_mem_closure_diff {G : Type*} [Group G] {Δ : Set G} {n v : G}
    (hΔ : MulAut.conj n '' Δ = Δ) (hv : v ∈ Subgroup.closure (Δ \ {v})) :
    n * v * n⁻¹ ∈ Subgroup.closure (Δ \ {n * v * n⁻¹}) := by
  have h := (mem_closure_image_diff_iff (f := (MulAut.conj n).toMonoidHom)
    (MulAut.conj n).injective (S := Δ) (x := v)).mpr hv
  change n * v * n⁻¹ ∈ Subgroup.closure (MulAut.conj n '' Δ \ {n * v * n⁻¹}) at h
  rwa [hΔ] at h

end CFSG.GroupTheory
