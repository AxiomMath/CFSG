module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GroupTheory.ZJ

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem normal_p_quotient_frattini {p : ℕ} [Fact p.Prime] {C H : Subgroup G} [C.Normal]
    [H.Normal] (hCH : C ≤ H) (hp : IsPGroup p (H ⧸ C.subgroupOf H)) (P : Sylow p H) :
    (H : Set G) = (C : Set G) * ((P : Subgroup H).map H.subtype : Set G) ∧
      (C : Set G) * (normalizer ((P : Subgroup H).map H.subtype : Set G) : Set G) =
        Set.univ := by
  set P' : Subgroup G := (P : Subgroup H).map H.subtype with hP'
  have hP'H : P' ≤ H := map_subtype_le _
  have hCP : (H : Set G) = (C : Set G) * (P' : Set G) := by
    apply Set.Subset.antisymm
    · intro h hh
      let f := QuotientGroup.mk' (C.subgroupOf H)
      have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
      let Q := P.mapSurjective hf
      have hQ : (Q : Subgroup (H ⧸ C.subgroupOf H)) = ⊤ :=
        (Q.is_maximal' (hp.to_subgroup ⊤) le_top).symm
      have hmem : f ⟨h, hh⟩ ∈ (Q : Subgroup (H ⧸ C.subgroupOf H)) := by
        rw [hQ]
        exact mem_top _
      obtain ⟨x, hx, hxh⟩ := Subgroup.mem_map.mp hmem
      have hxC : x⁻¹ * ⟨h, hh⟩ ∈ C.subgroupOf H := (QuotientGroup.eq).mp hxh
      have hhx : h * (x : G)⁻¹ ∈ C := by
        have h1 : (x : G)⁻¹ * h ∈ C := hxC
        have h2 := (inferInstance : C.Normal).conj_mem _ h1 (x : G)
        rwa [mul_inv_cancel_left] at h2
      exact ⟨h * (x : G)⁻¹, hhx, x, ⟨x, hx, rfl⟩, inv_mul_cancel_right h (x : G)⟩
    · rintro _ ⟨c, hc, y, hy, rfl⟩
      exact H.mul_mem (hCH hc) (hP'H hy)
  refine ⟨hCP, Set.eq_univ_of_forall fun g => ?_⟩
  have htop := Sylow.normalizer_sup_eq_top P
  have hg : g ∈ ((normalizer (P' : Set G) ⊔ H : Subgroup G) : Set G) := by
    rw [← hP'] at htop
    rw [htop]
    exact mem_top g
  rw [mul_normal] at hg
  obtain ⟨n, hn, h, hh, rfl⟩ := hg
  rw [hCP] at hh
  obtain ⟨c, hc, y, hy, rfl⟩ := hh
  refine ⟨n * c * n⁻¹, (inferInstance : C.Normal).conj_mem c hc n, n * y,
    (normalizer (P' : Set G)).mul_mem hn (le_normalizer hy), ?_⟩
  group

end CFSG.GroupTheory.ZJ
