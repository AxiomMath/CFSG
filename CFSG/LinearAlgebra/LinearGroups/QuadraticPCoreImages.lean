module

public import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticPGroupImages
public import CFSG.GroupTheory.BaerConjugatePairPCore

public section

namespace CFSG.LinearGroups

universe v

theorem quadratic_image_mem_pCore_of_pairs {G : Type*} [Group G] [Finite G] {F : Type*}
    [Field F] {p : ℕ} (hp : p.Prime) [CharP F p] {V : Type v} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    (hpair : ∀ (a b : G)
      (σ : Subgroup.closure ({a, b} : Set G) →* LinearMap.GeneralLinearGroup F V),
      ((σ ⟨a, Subgroup.subset_closure (Set.mem_insert _ _)⟩ : V →ₗ[F] V) - 1) ^ 2 = 0 →
      ((σ ⟨b, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩ :
        V →ₗ[F] V) - 1) ^ 2 = 0 → IsPGroup p σ.range)
    (H : Subgroup G) (ρ : H →* LinearMap.GeneralLinearGroup F V) (x : H)
    (hx : ((ρ x : V →ₗ[F] V) - 1) ^ 2 = 0) : ρ.rangeRestrict x ∈ CFSG.pCore p ρ.range := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite ρ.range := Finite.of_surjective _ ρ.rangeRestrict_surjective
  refine (CFSG.GroupTheory.baer_conjugate_pair_p_core p).2 _ fun δ => ?_
  obtain ⟨h, rfl⟩ := ρ.rangeRestrict_surjective δ
  have hLH : Subgroup.closure ({(x : G), ((h⁻¹ * x * h : H) : G)} : Set G) ≤ H := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact x.2
    · exact (h⁻¹ * x * h).2
  let σ := ρ.comp (Subgroup.inclusion hLH)
  have hσa : σ ⟨(x : G), Subgroup.subset_closure (Set.mem_insert _ _)⟩ = ρ x := rfl
  have hσb : σ ⟨((h⁻¹ * x * h : H) : G),
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩ =
      ρ (h⁻¹ * x * h) := rfl
  have hconj : ((ρ (h⁻¹ * x * h) : V →ₗ[F] V) - 1) ^ 2 = 0 := by
    rw [map_mul, map_mul, map_inv]
    exact (quadratic_linear_p_elements p (ρ x) hx).2 (ρ h)
  have hP := hpair (x : G) ((h⁻¹ * x * h : H) : G) σ (by rw [hσa]; exact hx)
    (by rw [hσb]; exact hconj)
  set C := Subgroup.closure ({ρ.rangeRestrict x,
    (ρ.rangeRestrict h)⁻¹ * ρ.rangeRestrict x * ρ.rangeRestrict h} : Set ρ.range) with hC
  have hel : ρ.range.subtype ((ρ.rangeRestrict h)⁻¹ * ρ.rangeRestrict x * ρ.rangeRestrict h) =
      ρ (h⁻¹ * x * h) := by
    simp
  have hmap : C.map ρ.range.subtype = σ.range := by
    rw [hC, MonoidHom.map_closure, Set.image_pair, range_eq_closure_pair, hσa, hσb, hel]
    rfl
  rw [← hmap] at hP
  exact hP.of_equiv (C.equivMapOfInjective ρ.range.subtype ρ.range.subtype_injective).symm

theorem dihedral_subgroup_quadratic_linear_image_in_p_core {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) {n : ℕ} (hn : 2 ≤ n)
    (hS : Nonempty (DihedralGroup (2 ^ (n - 1)) ≃* (S : Subgroup G))) (H : Subgroup G)
    {F : Type*} [Field F] {p : ℕ} (hp : p.Prime) (hodd : Odd p) [CharP F p] {V : Type v}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : H →* LinearMap.GeneralLinearGroup F V) :
    ∀ x : H, ((ρ x : V →ₗ[F] V) - 1) ^ 2 = 0 → ρ.rangeRestrict x ∈ CFSG.pCore p ρ.range :=
  fun x hx => quadratic_image_mem_pCore_of_pairs hp (fun a b σ ha hb =>
    (dihedral_two_quadratic_generator_images_are_p_groups S hn hS hp hodd a b σ ha hb).2) H ρ x
    hx

theorem cyclic_unique_involution_two_sections_give_quadratic_p_core_images {G : Type*}
    [Group G] [Finite G]
    (hsec : ∀ D : Subgroup G, IsPGroup 2 D → ∀ (E : Subgroup D) [E.Normal],
      (∀ u v : D ⧸ E, orderOf u = 2 → orderOf v = 2 → u = v) → IsCyclic (D ⧸ E))
    (H : Subgroup G) {F : Type*} [Field F] {p : ℕ} (hp : p.Prime) (hodd : Odd p) [CharP F p]
    {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : H →* LinearMap.GeneralLinearGroup F V) :
    ∀ x : H, ((ρ x : V →ₗ[F] V) - 1) ^ 2 = 0 → ρ.rangeRestrict x ∈ CFSG.pCore p ρ.range :=
  fun x hx => quadratic_image_mem_pCore_of_pairs hp (fun a b σ ha hb =>
    (cyclic_unique_involution_two_sections_give_quadratic_p_group_images hsec hp hodd a b σ ha
      hb).2) H ρ x hx

end CFSG.LinearGroups
