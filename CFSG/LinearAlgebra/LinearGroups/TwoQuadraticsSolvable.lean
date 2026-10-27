module

public import CFSG.LinearAlgebra.LinearGroups.QuadraticActions

public section

namespace CFSG.LinearGroups

open Matrix
open scoped LinearAlgebra.Projectivization MatrixGroups

universe u v

variable {K : Type u} [Field K]

section Helpers

variable {V : Type v} [AddCommGroup V] [Module K V]

theorem eq_one_of_quadratic_of_finrank_le_one [FiniteDimensional K V]
    (hV : Module.finrank K V ≤ 1) {a : LinearMap.GeneralLinearGroup K V}
    (ha : ((a : V →ₗ[K] V) - 1) ^ 2 = 0) : a = 1 := by
  obtain ⟨N, hNdef⟩ : ∃ N : Module.End K V, N = (a : V →ₗ[K] V) - 1 := ⟨_, rfl⟩
  have hN : N * N = 0 := by rw [hNdef, ← sq]; exact ha
  have hle : LinearMap.range N ≤ LinearMap.ker N := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, ← Module.End.mul_apply, hN, LinearMap.zero_apply]
  have h1 := LinearMap.finrank_range_add_finrank_ker N
  have h2 := Submodule.finrank_mono hle
  have h3 : Module.finrank K (LinearMap.range N) = 0 := by omega
  have hN0 : N = 0 := by
    rw [← LinearMap.range_eq_bot]
    exact Submodule.finrank_eq_zero.mp h3
  apply Units.ext
  rw [Units.val_one]
  rw [hNdef, sub_eq_zero] at hN0
  exact hN0

theorem range_eq_closure_pair {G G' : Type*} [Group G] [Group G'] (a b : G)
    (f : Subgroup.closure ({a, b} : Set G) →* G') :
    f.range = Subgroup.closure {f ⟨a, Subgroup.subset_closure (by simp)⟩,
      f ⟨b, Subgroup.subset_closure (by simp)⟩} := by
  rw [MonoidHom.range_eq_map, ← Subgroup.closure_closure_coe_preimage (k := ({a, b} : Set G)),
    MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, hx | hx, rfl⟩
    · left
      congr 1
      exact Subtype.ext hx
    · right
      congr 1
      exact Subtype.ext hx
  · rintro (rfl | rfl)
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr rfl, rfl⟩

theorem invariantRestrict_quadratic (H : Subgroup (LinearMap.GeneralLinearGroup K V))
    (W : Submodule K V) (hW : ∀ g ∈ H, ∀ w ∈ W, (g : V →ₗ[K] V) w ∈ W) (g : H)
    (hg : ((g.1 : V →ₗ[K] V) - 1) ^ 2 = 0) :
    (((invariantRestrict H W hW g : LinearMap.GeneralLinearGroup K W) : W →ₗ[K] W) - 1) ^ 2 =
      0 := by
  ext w
  have := congrArg (fun φ : Module.End K V => φ w) hg
  simpa [sq, coe_invariantRestrict_apply, map_sub] using this

theorem invariantQuotient_quadratic (H : Subgroup (LinearMap.GeneralLinearGroup K V))
    (W : Submodule K V) (hW : ∀ g ∈ H, ∀ w ∈ W, (g : V →ₗ[K] V) w ∈ W) (g : H)
    (hg : ((g.1 : V →ₗ[K] V) - 1) ^ 2 = 0) :
    (((invariantQuotient H W hW g : LinearMap.GeneralLinearGroup K (V ⧸ W)) :
      (V ⧸ W) →ₗ[K] V ⧸ W) - 1) ^ 2 = 0 := by
  ext v
  have := congrArg (fun φ : Module.End K V => φ v) hg
  simp only [sq, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.zero_apply, map_sub] at this
  simp only [sq, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, invariantQuotient_apply_mk,
    LinearMap.zero_apply, ← Submodule.Quotient.mk_sub, map_sub]
  rw [this, Submodule.Quotient.mk_zero]

end Helpers

section DimTwo

variable {V : Type v} [AddCommGroup V] [Module K V]

theorem exists_invariant_line_of_finrank_two [IsAlgClosed K] {p : ℕ} (hp : p.Prime)
    (hodd : Odd p) [CharP K p] [FiniteDimensional K V] (hV : Module.finrank K V = 2)
    (a b : LinearMap.GeneralLinearGroup K V) (ha : ((a : V →ₗ[K] V) - 1) ^ 2 = 0)
    (hb : ((b : V →ₗ[K] V) - 1) ^ 2 = 0)
    [Finite (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V)))]
    (hsolv : Group.IsSolvable
      (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))))
    (halt : 5 ≤ p ∨
      Odd (Nat.card (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))))) :
    ∃ L : Submodule K V, Module.finrank K L = 1 ∧ (∀ v ∈ L, (a : V →ₗ[K] V) v ∈ L) ∧
      ∀ v ∈ L, (b : V →ₗ[K] V) v ∈ L := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let e : Module.Basis (Fin 2) K V := Module.finBasisOfFinrankEq K V hV
  let σ : LinearMap.GeneralLinearGroup K V ≃* GL (Fin 2) K :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv e).toRingEquiv.toMulEquiv
  have hσ : ∀ g, ((σ g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      LinearMap.toMatrix e e (g : V →ₗ[K] V) := fun _ => rfl
  let Φ : LinearMap.GeneralLinearGroup K V →* PGL(Fin 2, K) :=
    (ProjGenLinGroup.mk).comp σ.toMonoidHom
  have : Finite ((Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))).map Φ) :=
    Finite.of_surjective _ (Φ.subgroupMap_surjective _)
  have hsolv' : Group.IsSolvable
      ((Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))).map Φ) :=
    Group.isSolvable_of_surjective (Φ.subgroupMap_surjective _)
  have halt' : 5 ≤ p ∨ Odd (Nat.card
      ((Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))).map Φ)) := by
    rcases halt with h | h
    · exact Or.inl h
    · exact Or.inr (Odd.of_dvd_nat h (Subgroup.card_map_dvd _ Φ))
  have hpow : ∀ g : LinearMap.GeneralLinearGroup K V, ((g : V →ₗ[K] V) - 1) ^ 2 = 0 →
      (Φ g) ^ p ^ 1 = 1 := fun g hg => by
    rw [pow_one, ← map_pow, (quadratic_linear_p_elements p g hg).1, map_one]
  have hgen : (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))).map Φ =
      Subgroup.closure {h | h ∈ (Subgroup.closure
        ({a, b} : Set (LinearMap.GeneralLinearGroup K V))).map Φ ∧ ∃ k : ℕ, h ^ p ^ k = 1} := by
    apply le_antisymm
    · rw [MonoidHom.map_closure, Set.image_pair]
      apply Subgroup.closure_mono
      rintro _ (rfl | rfl)
      · exact ⟨Subgroup.subset_closure (Set.mem_insert _ _), 1, hpow a ha⟩
      · exact ⟨Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)), 1,
          hpow b hb⟩
    · exact (Subgroup.closure_le _).mpr fun h hh => hh.1
  obtain ⟨x, hx⟩ := solvable_projective_p_generated_fixed_point hp hodd _ hgen halt'
  induction x using Projectivization.ind with
  | h v hv =>
  have hline : ∀ g : LinearMap.GeneralLinearGroup K V,
      Φ g • Projectivization.mk K v hv = Projectivization.mk K v hv →
      ∀ w ∈ K ∙ e.equivFun.symm v, (g : V →ₗ[K] V) w ∈ K ∙ e.equivFun.symm v := by
    intro g hg w hw
    obtain ⟨c, hc⟩ := (mk_smul_mk_eq_iff (σ g) hv).mp hg
    have hgy : (g : V →ₗ[K] V) (e.equivFun.symm v) = c • e.equivFun.symm v := by
      apply e.equivFun.injective
      have h1 := LinearMap.toMatrix_mulVec_repr e e (g : V →ₗ[K] V) (e.equivFun.symm v)
      have h2 : ⇑(e.repr (e.equivFun.symm v)) = v := by
        rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
      rw [← hσ, h2, hc] at h1
      rw [Module.Basis.equivFun_apply, ← h1, map_smul, LinearEquiv.apply_symm_apply]
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul, hgy, smul_smul]
    exact Submodule.mem_span_singleton.mpr ⟨t * c, rfl⟩
  have hy0 : e.equivFun.symm v ≠ 0 := by
    intro h0
    apply hv
    rw [← e.equivFun.apply_symm_apply v, h0, map_zero]
  refine ⟨K ∙ e.equivFun.symm v, finrank_span_singleton hy0,
    hline a (hx _ (Subgroup.mem_map_of_mem Φ (Subgroup.subset_closure (Set.mem_insert a {b})))),
    hline b (hx _ (Subgroup.mem_map_of_mem Φ
      (Subgroup.subset_closure (Set.mem_insert_of_mem a (Set.mem_singleton b)))))⟩

end DimTwo

theorem two_quadratics_solvable_algebraically_closed [IsAlgClosed K] {p : ℕ} (hp : p.Prime)
    (hodd : Odd p) [CharP K p] {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (a b : LinearMap.GeneralLinearGroup K V) (ha : ((a : V →ₗ[K] V) - 1) ^ 2 = 0)
    (hb : ((b : V →ₗ[K] V) - 1) ^ 2 = 0)
    [Finite (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V)))]
    (hsolv : Group.IsSolvable
      (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))))
    (halt : 5 ≤ p ∨
      Odd (Nat.card (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))))) :
    IsPGroup p (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))) := by
  have : Fact p.Prime := ⟨hp⟩
  suffices key : ∀ n : ℕ, ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      Module.finrank K V = n → ∀ a b : LinearMap.GeneralLinearGroup K V,
      ((a : V →ₗ[K] V) - 1) ^ 2 = 0 → ((b : V →ₗ[K] V) - 1) ^ 2 = 0 →
      Finite (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))) →
      Group.IsSolvable (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))) →
      (5 ≤ p ∨
        Odd (Nat.card (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))))) →
      IsPGroup p (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))) from
    key _ V rfl a b ha hb inferInstance hsolv halt
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hVn a b ha hb hfin hsolv halt
  have hbot : ∀ (G : Type v) [Group G] (H : Subgroup G), H = ⊥ → IsPGroup p H := by
    intro G _ H hH g
    refine ⟨0, ?_⟩
    rw [pow_zero, pow_one]
    exact Subtype.ext (Subgroup.mem_bot.mp (hH ▸ g.2))
  by_cases hred : ∃ W : Submodule K V, W ≠ ⊥ ∧ W ≠ ⊤ ∧ (∀ v ∈ W, (a : V →ₗ[K] V) v ∈ W) ∧
      ∀ v ∈ W, (b : V →ₗ[K] V) v ∈ W
  · obtain ⟨W, hW0, hWt, haW, hbW⟩ := hred
    have hWH : ∀ g ∈ Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V)),
        ∀ w ∈ W, (g : V →ₗ[K] V) w ∈ W := fun g hg =>
      mapsTo_of_mem_closure (by
        rintro s (rfl | rfl)
        · exact haW
        · exact hbW) hg
    have hdimW : Module.finrank K W < n := hVn ▸ Submodule.finrank_lt hWt
    have hdimQ : Module.finrank K (V ⧸ W) < n := by
      have h1 := Submodule.finrank_quotient_add_finrank W
      have h2 : 0 < Module.finrank K W :=
        Nat.pos_of_ne_zero fun h => hW0 (Submodule.finrank_eq_zero.mp h)
      omega
    have hrestr : ∀ (U : Type v) [AddCommGroup U] [Module K U] [FiniteDimensional K U],
        Module.finrank K U < n →
        ∀ ρ : Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V)) →*
          LinearMap.GeneralLinearGroup K U,
        ((ρ ⟨a, Subgroup.subset_closure (Set.mem_insert _ _)⟩ :
          LinearMap.GeneralLinearGroup K U) - 1 : Module.End K U) ^ 2 = 0 →
        ((ρ ⟨b, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩ :
          LinearMap.GeneralLinearGroup K U) - 1 : Module.End K U) ^ 2 = 0 →
        IsPGroup p ρ.range := by
      intro U _ _ _ hU ρ hρa hρb
      have hfin' : Finite ρ.range := Finite.of_surjective _ ρ.rangeRestrict_surjective
      have hsolv' : Group.IsSolvable ρ.range :=
        Group.isSolvable_of_surjective ρ.rangeRestrict_surjective
      have halt' : 5 ≤ p ∨ Odd (Nat.card ρ.range) := by
        rcases halt with h | h
        · exact Or.inl h
        · exact Or.inr (Odd.of_dvd_nat h (Subgroup.card_range_dvd ρ))
      rw [range_eq_closure_pair] at hfin' hsolv' halt' ⊢
      exact ih _ hU U rfl _ _ hρa hρb hfin' hsolv' halt'
    exact linear_p_extension _ W p hWH
      (hrestr W hdimW _ (invariantRestrict_quadratic _ W hWH _ ha)
        (invariantRestrict_quadratic _ W hWH _ hb))
      (hrestr (V ⧸ W) hdimQ _ (invariantQuotient_quadratic _ W hWH _ ha)
        (invariantQuotient_quadratic _ W hWH _ hb))
  ·
    have hab1 : Module.finrank K V ≤ 1 → IsPGroup p
        (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))) := by
      intro h1
      apply hbot
      rw [eq_one_of_quadratic_of_finrank_le_one h1 ha, eq_one_of_quadratic_of_finrank_le_one h1 hb,
        Set.pair_eq_singleton, Subgroup.closure_singleton_one]
    by_cases hV1 : Module.finrank K V ≤ 1
    · exact hab1 hV1
    have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (M := V) (by omega)
    have hirr : ∀ W : Submodule K V, (∀ g ∈ Subgroup.closure
        ({a, b} : Set (LinearMap.GeneralLinearGroup K V)), ∀ w ∈ W, (g : V →ₗ[K] V) w ∈ W) →
        W = ⊥ ∨ W = ⊤ := by
      intro W hW
      by_contra hne
      push Not at hne
      exact hred ⟨W, hne.1, hne.2, hW a (Subgroup.subset_closure (Set.mem_insert _ _)),
        hW b (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))⟩
    have hle2 := two_quadratic_irreducible_dimension a b ha hb hirr
    have hV2 : Module.finrank K V = 2 := by omega
    obtain ⟨L, hL1, haL, hbL⟩ :=
      exists_invariant_line_of_finrank_two hp hodd hV2 a b ha hb hsolv halt
    exfalso
    apply hred
    refine ⟨L, ?_, ?_, haL, hbL⟩
    · intro h
      rw [h, finrank_bot] at hL1
      exact zero_ne_one hL1
    · intro h
      rw [h, finrank_top, hV2] at hL1
      norm_num at hL1

end CFSG.LinearGroups
