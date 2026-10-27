module

public import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticFieldEmbedding
public import CFSG.LinearAlgebra.LinearGroups.QuadraticActions
public import CFSG.LinearAlgebra.LinearGroups.RegularPermutationSign
public import Mathlib.Algebra.CharP.Algebra

public section

namespace CFSG.LinearGroups

open Matrix

universe v

theorem SL2_coe_eq_neg_one_of_sq {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) (hA : A ^ 2 = 1) (hA1 : A ≠ 1) :
    (A : Matrix (Fin 2) (Fin 2) K) = -1 := by
  have hdet : (A : Matrix (Fin 2) (Fin 2) K).det = 1 := A.2
  have hsq : (A : Matrix (Fin 2) (Fin 2) K) * A = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← sq, hA, Matrix.SpecialLinearGroup.coe_one]
  have e00 := congrFun (congrFun hsq 0) 0
  have e01 := congrFun (congrFun hsq 0) 1
  have e10 := congrFun (congrFun hsq 1) 0
  have e11 := congrFun (congrFun hsq 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hdet
  have htr : A 0 0 + A 1 1 ≠ 0 := by
    intro h0
    apply h2
    linear_combination -e00 - hdet + A 0 0 * h0
  have hβ : A 0 1 = 0 := by
    have : A 0 1 * (A 0 0 + A 1 1) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right htr
  have hγ : A 1 0 = 0 := by
    have : A 1 0 * (A 0 0 + A 1 1) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right htr
  rw [hβ, hγ] at hdet e00 e11
  have hαδ : A 0 0 = A 1 1 := by
    have h1 : A 0 0 * (A 0 0 - A 1 1) = 0 := by linear_combination e00 - hdet
    have hα0 : A 0 0 ≠ 0 := by
      intro h
      rw [h] at e00
      simp at e00
    exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hα0)
  have hα : A 0 0 = 1 ∨ A 0 0 = -1 := by
    have : (A 0 0 - 1) * (A 0 0 + 1) = 0 := by linear_combination e00
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hα with h1 | h1
  · exfalso
    apply hA1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, hβ, hγ, ← hαδ]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, hβ, hγ, ← hαδ]

theorem two_quadratic_unique_involution {J : Type*} [Group J] {F : Type*} [Field F] {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) [CharP F p] {V : Type v} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Nontrivial V] (ρ : J →* LinearMap.GeneralLinearGroup F V)
    (hρ : Function.Injective ρ)
    (hirr : ∀ W : Submodule F V, (∀ g : J, ∀ w ∈ W, (ρ g : V →ₗ[F] V) w ∈ W) → W = ⊥ ∨ W = ⊤)
    (a b : J) (hab : Subgroup.closure ({a, b} : Set J) = ⊤) (hX1 : ρ a ≠ 1) (hY1 : ρ b ≠ 1)
    (hX : ((ρ a : V →ₗ[F] V) - 1) ^ 2 = 0) (hY : ((ρ b : V →ₗ[F] V) - 1) ^ 2 = 0) :
    ∀ x y : J, orderOf x = 2 → orderOf y = 2 → x = y := by
  have hmem : ∀ g : J,
      ρ g ∈ Subgroup.closure ({ρ a, ρ b} : Set (LinearMap.GeneralLinearGroup F V)) := by
    intro g
    have : ρ g ∈ (Subgroup.closure ({a, b} : Set J)).map ρ := by
      rw [hab]
      exact ⟨g, Subgroup.mem_top g, rfl⟩
    rwa [MonoidHom.map_closure, Set.image_pair] at this
  have hirr' : ∀ W : Submodule F V, (∀ w ∈ W, (ρ a : V →ₗ[F] V) w ∈ W) →
      (∀ w ∈ W, (ρ b : V →ₗ[F] V) w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hXW hYW
    refine hirr W fun g => mapsTo_of_mem_closure ?_ (hmem g)
    rintro s (rfl | rfl)
    · exact hXW
    · exact hYW
  obtain ⟨K, _, _, lam, h, -, -, -, -, -, -, -, ⟨ψ, -⟩, -⟩ :=
    irreducible_two_quadratic_generators_field_embedding (ρ a) (ρ b) hX1 hY1 hX hY hirr'
  have : CharP K p := charP_of_injective_algebraMap (algebraMap F K).injective p
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have h2' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff K p] at h2'
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2'
    rw [this] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) even_two
  have hneg : ∀ x : J, orderOf x = 2 →
      (((ψ ⟨ρ x, hmem x⟩ : Subgroup.closure ({slUpper K, slLower lam} :
        Set (Matrix.SpecialLinearGroup (Fin 2) K))) : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) = -1 := by
    intro x hx
    have hord : orderOf (((ψ ⟨ρ x, hmem x⟩ : Subgroup.closure ({slUpper K, slLower lam} :
        Set (Matrix.SpecialLinearGroup (Fin 2) K))) : Matrix.SpecialLinearGroup (Fin 2) K)) =
        2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk,
        orderOf_injective ρ hρ, hx]
    refine SL2_coe_eq_neg_one_of_sq h2 _ ?_ ?_
    · have := pow_orderOf_eq_one (((ψ ⟨ρ x, hmem x⟩ : Subgroup.closure ({slUpper K, slLower lam} :
        Set (Matrix.SpecialLinearGroup (Fin 2) K))) : Matrix.SpecialLinearGroup (Fin 2) K))
      rwa [hord] at this
    · intro h1
      rw [h1, orderOf_one] at hord
      exact absurd hord (by norm_num)
  intro x y hx hy
  apply hρ
  have hxy : (⟨ρ x, hmem x⟩ : Subgroup.closure ({ρ a, ρ b} :
      Set (LinearMap.GeneralLinearGroup F V))) = ⟨ρ y, hmem y⟩ := by
    apply ψ.injective
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [hneg x hx, hneg y hy]
  exact congrArg Subtype.val hxy

theorem odd_card_of_cyclic_sylow_two {J : Type*} [Group J] [Finite J] (a b : J)
    (hab : Subgroup.closure ({a, b} : Set J) = ⊤) (ha : Odd (orderOf a)) (hb : Odd (orderOf b))
    (P : Sylow 2 J) (hP : IsCyclic P) : Odd (Nat.card J) := by
  classical
  have : Fintype J := Fintype.ofFinite J
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra heven
  rw [Nat.not_odd_iff_even] at heven
  let φ : J →* ℤˣ := Equiv.Perm.sign.comp (MulAction.toPermHom J J)
  have hφ : ∀ g : J, φ g = Equiv.Perm.sign (Equiv.mulLeft g) := fun g => rfl
  have hodd1 : ∀ g : J, Odd (orderOf g) → φ g = 1 := by
    intro g hg
    rcases Int.units_eq_one_or (φ g) with h | h
    · exact h
    · exfalso
      have := congrArg φ (pow_orderOf_eq_one g)
      rw [map_pow, h, hg.neg_one_pow, map_one] at this
      exact absurd this (by decide)
  have hφ1 : ∀ g : J, φ g = 1 := by
    intro g
    have hle : Subgroup.closure ({a, b} : Set J) ≤ φ.ker := by
      rw [Subgroup.closure_le]
      rintro s (rfl | rfl)
      · exact hodd1 _ ha
      · exact hodd1 _ hb
    rw [hab] at hle
    exact hle (Subgroup.mem_top g)
  obtain ⟨z, hz⟩ := hP.exists_generator
  have hzord : orderOf (z : J) = 2 ^ (Nat.card J).factorization 2 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hz, P.card_eq_multiplicity]
  have hcard0 : Nat.card J ≠ 0 := Nat.card_pos.ne'
  have hk : 1 ≤ (Nat.card J).factorization 2 :=
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hcard0).mp (even_iff_two_dvd.mp heven)
  have hcompl : Odd (Nat.card J / 2 ^ (Nat.card J).factorization 2) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Nat.not_dvd_ordCompl Nat.prime_two hcard0))
  obtain ⟨-, -, hsign⟩ := regular_permutation_sign (z : J)
  rw [hzord, ← Nat.card_eq_fintype_card] at hsign
  have hdiff : Odd (Nat.card J - Nat.card J / 2 ^ (Nat.card J).factorization 2) :=
    Nat.Even.sub_odd (Nat.div_le_self _ _) heven hcompl
  rw [hdiff.neg_one_pow] at hsign
  have := hφ1 (z : J)
  rw [hφ, hsign] at this
  exact absurd this (by decide)

theorem exists_two_subgroup_onto_sylow {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (N : Subgroup H) [N.Normal] :
    ∃ (D : Subgroup G) (T : Sylow 2 (H ⧸ N)) (f : D →* (T : Subgroup (H ⧸ N))),
      IsPGroup 2 D ∧ Function.Surjective f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D₀⟩ := (inferInstance : Nonempty (Sylow 2 H))
  let T := D₀.mapSurjective (QuotientGroup.mk'_surjective N)
  let e := Subgroup.equivMapOfInjective (D₀ : Subgroup H) H.subtype H.subtype_injective
  refine ⟨(D₀ : Subgroup H).map H.subtype, T,
    ((QuotientGroup.mk' N).subgroupMap (D₀ : Subgroup H)).comp e.symm.toMonoidHom,
    D₀.isPGroup'.map H.subtype, ?_⟩
  exact ((QuotientGroup.mk' N).subgroupMap_surjective _).comp e.symm.surjective

theorem odd_orderOf_of_quadratic {J : Type*} [Group J] {F : Type*} [Field F] {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) [CharP F p] {V : Type v} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (ρ : J →* LinearMap.GeneralLinearGroup F V)
    (hρ : Function.Injective ρ) {g : J} (hg : ((ρ g : V →ₗ[F] V) - 1) ^ 2 = 0) :
    Odd (orderOf g) := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : ρ (g ^ p) = 1 := by
    rw [map_pow]
    exact (quadratic_linear_p_elements p (ρ g) hg).1
  have h2 : g ^ p = 1 := hρ (h1.trans (map_one ρ).symm)
  exact Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one h2)

theorem cyclic_unique_involution_two_sections_give_odd_quadratic_sections {G : Type*} [Group G]
    [Finite G]
    (hsec : ∀ D : Subgroup G, IsPGroup 2 D → ∀ (E : Subgroup D) [E.Normal],
      (∀ u v : D ⧸ E, orderOf u = 2 → orderOf v = 2 → u = v) → IsCyclic (D ⧸ E))
    (H : Subgroup G) (N : Subgroup H) [N.Normal] {F : Type*} [Field F] {p : ℕ} (hp : p.Prime)
    (hodd : Odd p) [CharP F p] {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [Nontrivial V] (ρ : H ⧸ N →* LinearMap.GeneralLinearGroup F V) (hρ : Function.Injective ρ)
    (hirr : ∀ W : Submodule F V, (∀ g : H ⧸ N, ∀ w ∈ W, (ρ g : V →ₗ[F] V) w ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (a b : H ⧸ N) (hab : Subgroup.closure ({a, b} : Set (H ⧸ N)) = ⊤) (hX1 : ρ a ≠ 1)
    (hY1 : ρ b ≠ 1) (hX : ((ρ a : V →ₗ[F] V) - 1) ^ 2 = 0)
    (hY : ((ρ b : V →ₗ[F] V) - 1) ^ 2 = 0) :
    Odd (Nat.card (H ⧸ N)) := by
  have huniq := two_quadratic_unique_involution hp hodd ρ hρ hirr a b hab hX1 hY1 hX hY
  obtain ⟨D, T, f, hDp, hf⟩ := exists_two_subgroup_onto_sylow H N
  have hTuniq : ∀ u v : (T : Subgroup (H ⧸ N)), orderOf u = 2 → orderOf v = 2 → u = v :=
    fun u v hu hv => Subtype.ext (huniq u v (by rw [Subgroup.orderOf_coe]; exact hu)
      (by rw [Subgroup.orderOf_coe]; exact hv))
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hcyc : IsCyclic (D ⧸ f.ker) := hsec D hDp f.ker fun u v hu hv =>
    e.injective (hTuniq _ _ (by rw [MulEquiv.orderOf_eq]; exact hu)
      (by rw [MulEquiv.orderOf_eq]; exact hv))
  exact odd_card_of_cyclic_sylow_two a b hab (odd_orderOf_of_quadratic hp hodd ρ hρ hX)
    (odd_orderOf_of_quadratic hp hodd ρ hρ hY) T ((MulEquiv.isCyclic e).mp hcyc)

end CFSG.LinearGroups
