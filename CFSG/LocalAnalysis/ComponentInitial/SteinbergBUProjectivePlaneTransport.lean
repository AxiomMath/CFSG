module

public import CFSG.LinearAlgebra.ProjectivePrimePlane

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix Matrix.ProjGenLinGroup

variable {G Γ : Type*} [Group G] [Group Γ] {F : Type*} [Field F] {p : ℕ}

section Reindex

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

@[expose] def glReindex (e : ι ≃ κ) : GL ι F ≃* GL κ F :=
  Units.mapEquiv (Matrix.reindexAlgEquiv F F e).toMulEquiv

theorem coe_glReindex (e : ι ≃ κ) (g : GL ι F) :
    ((glReindex e g : GL κ F) : Matrix κ κ F) = Matrix.reindex e e (g : Matrix ι ι F) :=
  rfl

theorem glReindex_scalar (e : ι ≃ κ) (u : Fˣ) :
    glReindex e (GeneralLinearGroup.scalar ι u) = GeneralLinearGroup.scalar κ u := by
  ext i j
  rw [coe_glReindex, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar, scalar_apply,
    scalar_apply, reindex_apply, submatrix_diagonal_equiv]
  rfl

theorem glReindex_eq_scalar_iff (e : ι ≃ κ) (g : GL ι F) (u : Fˣ) :
    glReindex e g = GeneralLinearGroup.scalar κ u ↔ g = GeneralLinearGroup.scalar ι u := by
  rw [← glReindex_scalar e u, (glReindex e).injective.eq_iff]

end Reindex

abbrev projHom (τ : Γ →* GL (Fin p) F) : Γ →* ProjGenLinGroup (Fin p) F :=
  mk.comp τ

section Lift

variable (L : Γ →* G) (τ : Γ →* GL (Fin p) F)
  (hker : ∀ x, L x = 1 ↔ ∃ u : Fˣ, τ x = GeneralLinearGroup.scalar (Fin p) u)

include hker in
theorem ker_projHom : (projHom τ).ker = L.ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hker, MonoidHom.comp_apply, mk_eq_one,
    GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨fun ⟨u, hu⟩ => ⟨u, hu.symm⟩, fun ⟨u, hu⟩ => ⟨u, hu.symm⟩⟩

@[expose] noncomputable def rangeLift : (projHom τ).range →* G :=
  (projHom τ).rangeRestrict.liftOfSurjective (projHom τ).rangeRestrict_surjective
    ⟨L, by rw [MonoidHom.ker_rangeRestrict, ker_projHom L τ hker]⟩

theorem rangeLift_apply (x : Γ) :
    rangeLift L τ hker ((projHom τ).rangeRestrict x) = L x :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

theorem rangeLift_injective : Function.Injective (rangeLift L τ hker) := by
  rw [injective_iff_map_eq_one]
  intro j hj
  obtain ⟨x, rfl⟩ := (projHom τ).rangeRestrict_surjective j
  rw [rangeLift_apply] at hj
  have hx : x ∈ (projHom τ).ker := by
    rw [ker_projHom L τ hker]
    exact hj
  exact Subtype.ext hx

theorem range_rangeLift : (rangeLift L τ hker).range = L.range := by
  apply le_antisymm
  · rintro _ ⟨j, rfl⟩
    obtain ⟨x, rfl⟩ := (projHom τ).rangeRestrict_surjective j
    exact ⟨x, (rangeLift_apply L τ hker x).symm⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨_, rangeLift_apply L τ hker x⟩

end Lift

theorem plane_transport (hp : p.Prime) (L : Γ →* G) (τ : Γ →* GL (Fin p) F)
    (hτ : Function.Injective τ)
    (hker : ∀ x, L x = 1 ↔ ∃ u : Fˣ, τ x = GeneralLinearGroup.scalar (Fin p) u)
    (D : Subgroup G) (hDL : D ≤ L.range) (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hDp : ∀ x ∈ D, x ^ p = 1) (hcard : Nat.card D = p ^ 2)
    (hna : ¬ ∀ x ∈ D.comap L, ∀ y ∈ D.comap L, x * y = y * x) :
    ringChar F ≠ p ∧ (∀ x ∈ L.range, (∀ d ∈ D, d * x = x * d) → x ∈ D) ∧
      ∀ x y : Γ, Subgroup.closure {L x, L y} = D → ∃ ζ : F, IsPrimitiveRoot ζ p ∧
        (τ x : Matrix (Fin p) (Fin p) F) * τ y = ζ • ((τ y : Matrix (Fin p) (Fin p) F) * τ x) := by
  set J := (projHom τ).range
  set ι := rangeLift L τ hker
  have hι := rangeLift_apply L τ hker
  have hιinj := rangeLift_injective L τ hker
  have hιrange := range_rangeLift L τ hker
  set DJ := D.comap ι with hDJ
  set D' := DJ.map J.subtype with hD'
  have hDJmap : DJ.map ι = D := by
    rw [hDJ, Subgroup.map_comap_eq, hιrange, inf_eq_right.2 hDL]
  have hD'card : Nat.card D' = p ^ 2 := by
    rw [← hcard, ← hDJmap, Subgroup.card_map_of_injective hιinj,
      Subgroup.card_map_of_injective J.subtype_injective]
  have hD'ab : ∀ x ∈ D', ∀ y ∈ D', x * y = y * x := by
    rintro _ ⟨j, hj, rfl⟩ _ ⟨k, hk, rfl⟩
    have h := hDab _ hj _ hk
    rw [← map_mul, ← map_mul] at h
    change ((j * k : J) : ProjGenLinGroup (Fin p) F) = ((k * j : J) : ProjGenLinGroup (Fin p) F)
    rw [hιinj h]
  have hD'p : ∀ x ∈ D', x ^ p = 1 := by
    rintro _ ⟨j, hj, rfl⟩
    have h := hDp _ hj
    rw [← map_pow, ← map_one ι] at h
    change ((j ^ p : J) : ProjGenLinGroup (Fin p) F) = ((1 : J) : ProjGenLinGroup (Fin p) F)
    rw [hιinj h]
  have hτmem : ∀ x ∈ D.comap L, τ x ∈ D'.comap mk := fun x hx =>
    ⟨(projHom τ).rangeRestrict x, by
      change ι ((projHom τ).rangeRestrict x) ∈ D
      rw [hι]
      exact hx, rfl⟩
  have hD'na : ¬ ∀ x ∈ D'.comap mk, ∀ y ∈ D'.comap mk, x * y = y * x := fun hcomm =>
    hna fun x hx y hy => hτ (by rw [map_mul, map_mul]; exact hcomm _ (hτmem x hx) _ (hτmem y hy))
  obtain ⟨hchar, hcent, hbasis, -⟩ :=
    CFSG.LinearAlgebra.ProjectivePrimePlane.nonabelian_projective_prime_plane_self_centralizing hp
      D' hD'ab hD'p hD'card hD'na
  refine ⟨hchar, fun x hx hxD => ?_, fun x y hxy => ?_⟩
  ·
    rw [← hιrange] at hx
    obtain ⟨j, rfl⟩ := hx
    have hj : (j : ProjGenLinGroup (Fin p) F) ∈
        Subgroup.centralizer (D' : Set (ProjGenLinGroup (Fin p) F)) := by
      refine Subgroup.mem_centralizer_iff.2 ?_
      rintro _ ⟨k, hk, rfl⟩
      have h := hxD _ hk
      rw [← map_mul, ← map_mul] at h
      change ((k * j : J) : ProjGenLinGroup (Fin p) F) = ((j * k : J) : ProjGenLinGroup (Fin p) F)
      rw [hιinj h]
    rw [hcent] at hj
    obtain ⟨k, hk, hkj⟩ := hj
    rw [← Subtype.ext hkj]
    exact hk
  ·
    have hDJcl : Subgroup.closure {(projHom τ).rangeRestrict x, (projHom τ).rangeRestrict y} =
        DJ := by
      apply Subgroup.map_injective hιinj
      rw [MonoidHom.map_closure, Set.image_pair, hι, hι, hxy, hDJmap]
    have hcl : Subgroup.closure {mk (τ x), mk (τ y)} = D' := by
      rw [hD', ← hDJcl, MonoidHom.map_closure, Set.image_pair]
      rfl
    obtain ⟨ζ, hζ, h, -⟩ := hbasis _ (hcl ▸ Subgroup.subset_closure (by simp)) _
      (hcl ▸ Subgroup.subset_closure (by simp)) hcl (τ x) (τ y) rfl rfl
    exact ⟨ζ, hζ, h⟩

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
