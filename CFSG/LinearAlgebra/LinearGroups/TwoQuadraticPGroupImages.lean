module

public import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticDihedralSections
public import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticsSolvableLinear
public import CFSG.Milestones.OO_odd_order_solvable

public section

namespace CFSG.LinearGroups

universe v

theorem isPGroup_closure_one_pair {Γ : Type*} [Group Γ] {p : ℕ} (hp : p.Prime) {Y : Γ}
    (hY : Y ^ p = 1) : IsPGroup p (Subgroup.closure ({1, Y} : Set Γ)) := by
  rw [Subgroup.closure_insert_one, ← Subgroup.zpowers_eq_closure]
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hY) with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

theorem two_quadratic_images_isPGroup_of_odd_sections {G : Type*} [Group G] [Finite G]
    {F : Type*} [Field F] {p : ℕ} (hp : p.Prime) (hodd : Odd p) [CharP F p]
    (hsec : ∀ (H : Subgroup G) (N : Subgroup H) [N.Normal] (U : Type v) [AddCommGroup U]
      [Module F U] [FiniteDimensional F U] [Nontrivial U]
      (σ : H ⧸ N →* LinearMap.GeneralLinearGroup F U), Function.Injective σ →
      (∀ W : Submodule F U, (∀ g : H ⧸ N, ∀ w ∈ W, (σ g : U →ₗ[F] U) w ∈ W) →
        W = ⊥ ∨ W = ⊤) →
      ∀ x y : H ⧸ N, Subgroup.closure ({x, y} : Set (H ⧸ N)) = ⊤ → σ x ≠ 1 → σ y ≠ 1 →
        ((σ x : U →ₗ[F] U) - 1) ^ 2 = 0 → ((σ y : U →ₗ[F] U) - 1) ^ 2 = 0 →
        Odd (Nat.card (H ⧸ N)))
    {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (a b : G)
    (ρ : Subgroup.closure ({a, b} : Set G) →* LinearMap.GeneralLinearGroup F V)
    (hX : ((ρ ⟨a, Subgroup.subset_closure (Set.mem_insert _ _)⟩ : V →ₗ[F] V) - 1) ^ 2 = 0)
    (hY : ((ρ ⟨b, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩ :
      V →ₗ[F] V) - 1) ^ 2 = 0) :
    IsPGroup p ρ.range := by
  have : Fact p.Prime := ⟨hp⟩
  set a' : Subgroup.closure ({a, b} : Set G) := ⟨a, Subgroup.subset_closure (Set.mem_insert _ _)⟩
  set b' : Subgroup.closure ({a, b} : Set G) :=
    ⟨b, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
  suffices key : ∀ n : ℕ, ∀ (U : Type v) [AddCommGroup U] [Module F U] [FiniteDimensional F U],
      Module.finrank F U = n →
      ∀ σ : Subgroup.closure ({a, b} : Set G) →* LinearMap.GeneralLinearGroup F U,
      ((σ a' : U →ₗ[F] U) - 1) ^ 2 = 0 → ((σ b' : U →ₗ[F] U) - 1) ^ 2 = 0 →
      IsPGroup p σ.range from key _ V rfl ρ hX hY
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U _ _ _ hUn σ hσa hσb
  have hrange : σ.range = Subgroup.closure {σ a', σ b'} := range_eq_closure_pair a b σ
  have hfin : Finite σ.range := Finite.of_surjective _ σ.rangeRestrict_surjective
  by_cases hred : ∃ W : Submodule F U, W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ g ∈ σ.range, ∀ w ∈ W, (g : U →ₗ[F] U) w ∈ W
  ·
    obtain ⟨W, hW0, hWt, hW⟩ := hred
    have hdimW : Module.finrank F W < n := hUn ▸ Submodule.finrank_lt hWt
    have hdimQ : Module.finrank F (U ⧸ W) < n := by
      have h1 := Submodule.finrank_quotient_add_finrank W
      have h2 : 0 < Module.finrank F W :=
        Nat.pos_of_ne_zero fun h => hW0 (Submodule.finrank_eq_zero.mp h)
      omega
    have hcomp : ∀ {Q : Type v} [Group Q] (f : σ.range →* Q),
        (f.comp σ.rangeRestrict).range = f.range := fun f => by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr σ.rangeRestrict_surjective,
        ← MonoidHom.range_eq_map]
    have h1 := ih _ hdimW W rfl ((invariantRestrict σ.range W hW).comp σ.rangeRestrict)
      (invariantRestrict_quadratic σ.range W hW (σ.rangeRestrict a') hσa)
      (invariantRestrict_quadratic σ.range W hW (σ.rangeRestrict b') hσb)
    have h2 := ih _ hdimQ (U ⧸ W) rfl ((invariantQuotient σ.range W hW).comp σ.rangeRestrict)
      (invariantQuotient_quadratic σ.range W hW (σ.rangeRestrict a') hσa)
      (invariantQuotient_quadratic σ.range W hW (σ.rangeRestrict b') hσb)
    rw [hcomp] at h1 h2
    exact linear_p_extension σ.range W p hW h1 h2
  ·
    have hirr : ∀ W : Submodule F U, (∀ g ∈ σ.range, ∀ w ∈ W, (g : U →ₗ[F] U) w ∈ W) →
        W = ⊥ ∨ W = ⊤ := by
      intro W hW
      by_contra hne
      push Not at hne
      exact hred ⟨W, hne.1, hne.2, hW⟩
    have hpow : ∀ g : Subgroup.closure ({a, b} : Set G), ((σ g : U →ₗ[F] U) - 1) ^ 2 = 0 →
        σ g ^ p = 1 := fun g hg =>
      (quadratic_linear_p_elements p (σ g) hg).1
    by_cases hX1 : σ a' = 1
    · rw [hrange, hX1]
      exact isPGroup_closure_one_pair hp (hpow b' hσb)
    by_cases hY1 : σ b' = 1
    · rw [hrange, hY1, Set.pair_comm]
      exact isPGroup_closure_one_pair hp (hpow a' hσa)
    have hU1 : ¬ Module.finrank F U ≤ 1 := fun h =>
      hX1 (eq_one_of_quadratic_of_finrank_le_one h hσa)
    have : Nontrivial U := Module.nontrivial_of_finrank_pos (R := F) (M := U) (by omega)
    have hmk : ∀ g : Subgroup.closure ({a, b} : Set G),
        QuotientGroup.kerLift σ (g : _ ⧸ σ.ker) = σ g := QuotientGroup.kerLift_mk σ
    have hgen : Subgroup.closure ({(a' : _ ⧸ σ.ker), (b' : _ ⧸ σ.ker)} : Set (_ ⧸ σ.ker)) =
        ⊤ := by
      have h := range_eq_closure_pair a b (QuotientGroup.mk' σ.ker)
      rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)] at h
      exact h.symm
    have hirr' : ∀ W : Submodule F U, (∀ g : _ ⧸ σ.ker, ∀ w ∈ W,
        (QuotientGroup.kerLift σ g : U →ₗ[F] U) w ∈ W) → W = ⊥ ∨ W = ⊤ := by
      intro W hW
      apply hirr W
      rintro _ ⟨g, rfl⟩ w hw
      rw [← hmk]
      exact hW _ w hw
    have hoddJ := hsec _ σ.ker U (QuotientGroup.kerLift σ) (QuotientGroup.kerLift_injective σ)
      hirr' _ _ hgen (by rw [hmk]; exact hX1) (by rw [hmk]; exact hY1) (by rw [hmk]; exact hσa)
      (by rw [hmk]; exact hσb)
    have hoddΓ : Odd (Nat.card σ.range) := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange σ).toEquiv]
      exact hoddJ
    rw [hrange] at hoddΓ hfin ⊢
    exact two_quadratics_solvable_linear hp hodd (σ a') (σ b') hσa hσb
      (CFSG.Milestones.odd_order_solvable hoddΓ) (Or.inr hoddΓ)

theorem dihedral_two_quadratic_generator_images_are_p_groups {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) {n : ℕ} (hn : 2 ≤ n)
    (hS : Nonempty (DihedralGroup (2 ^ (n - 1)) ≃* (S : Subgroup G))) {F : Type*} [Field F]
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) [CharP F p] {V : Type v} [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (a b : G)
    (ρ : Subgroup.closure ({a, b} : Set G) →* LinearMap.GeneralLinearGroup F V)
    (hX : ((ρ ⟨a, Subgroup.subset_closure (Set.mem_insert _ _)⟩ : V →ₗ[F] V) - 1) ^ 2 = 0)
    (hY : ((ρ ⟨b, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩ :
      V →ₗ[F] V) - 1) ^ 2 = 0) :
    Finite ρ.range ∧ IsPGroup p ρ.range :=
  ⟨Finite.of_surjective _ ρ.rangeRestrict_surjective,
    two_quadratic_images_isPGroup_of_odd_sections hp hodd
      (fun H N _ _ _ _ _ _ σ hσ hirr x y hxy hx1 hy1 hx hy =>
        dihedral_sections_two_quadratic_generators_have_odd_order S hn hS H N hp hodd σ hσ hirr
          x y hxy hx1 hy1 hx hy) a b ρ hX hY⟩

theorem cyclic_unique_involution_two_sections_give_quadratic_p_group_images {G : Type*}
    [Group G] [Finite G]
    (hsec : ∀ D : Subgroup G, IsPGroup 2 D → ∀ (E : Subgroup D) [E.Normal],
      (∀ u v : D ⧸ E, orderOf u = 2 → orderOf v = 2 → u = v) → IsCyclic (D ⧸ E))
    {F : Type*} [Field F] {p : ℕ} (hp : p.Prime) (hodd : Odd p) [CharP F p] {V : Type v}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] (a b : G)
    (ρ : Subgroup.closure ({a, b} : Set G) →* LinearMap.GeneralLinearGroup F V)
    (hX : ((ρ ⟨a, Subgroup.subset_closure (Set.mem_insert _ _)⟩ : V →ₗ[F] V) - 1) ^ 2 = 0)
    (hY : ((ρ ⟨b, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩ :
      V →ₗ[F] V) - 1) ^ 2 = 0) :
    Finite ρ.range ∧ IsPGroup p ρ.range :=
  ⟨Finite.of_surjective _ ρ.rangeRestrict_surjective,
    two_quadratic_images_isPGroup_of_odd_sections hp hodd
      (fun H N _ _ _ _ _ _ σ hσ hirr x y hxy hx1 hy1 hx hy =>
        cyclic_unique_involution_two_sections_give_odd_quadratic_sections hsec H N hp hodd σ hσ
          hirr x y hxy hx1 hy1 hx hy) a b ρ hX hY⟩

end CFSG.LinearGroups
