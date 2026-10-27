module

public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.LocalAnalysis.ComponentInitial

variable {G : Type*} [Group G]

theorem commutator_le_of_forall_sq_mem {N : Subgroup G} [N.Normal] (h : ∀ g : G, g ^ 2 ∈ N) :
    commutator G ≤ N := by
  rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
  have hinv : ∀ x : G ⧸ N, x⁻¹ = x := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    apply inv_eq_of_mul_eq_one_right
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, ← pow_two]
    exact h g
  exact ⟨⟨fun a b => by rw [← hinv (a * b), mul_inv_rev, hinv, hinv]⟩⟩

theorem commutator_eq_of_isPerfect_of_forall_sq_mem {N : Subgroup G} [N.Normal]
    (hN : Group.IsPerfect N) (h : ∀ g : G, g ^ 2 ∈ N) : commutator G = N := by
  refine le_antisymm (commutator_le_of_forall_sq_mem h) ?_
  calc N = ⁅N, N⁆ := (Subgroup.isPerfect_iff.mp hN).symm
    _ ≤ commutator G := Subgroup.commutator_mono le_top le_top

theorem isPGroup_two_of_forall_sq_mem {N : Subgroup G} [N.Normal] (h : ∀ g : G, g ^ 2 ∈ N) :
    IsPGroup 2 (G ⧸ N) := by
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨1, ?_⟩
  rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact h g

theorem mem_of_isPGroup_two_of_orderOf_prime {N : Subgroup G} [N.Normal]
    (hN : IsPGroup 2 (G ⧸ N)) {g : G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hg : orderOf g = p) : g ∈ N := by
  obtain ⟨k, hk⟩ := hN (g : G ⧸ N)
  have h1 : orderOf (g : G ⧸ N) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf (g : G ⧸ N) ∣ p := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, ← hg, pow_orderOf_eq_one, QuotientGroup.mk_one]
  have hcop : Nat.Coprime p (2 ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have h3 : orderOf (g : G ⧸ N) = 1 := Nat.eq_one_of_dvd_coprimes hcop h2 h1
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem commutator_eq_map_symm {H : Type*} [Group H] (e : G ≃* H) :
    commutator G = (commutator H).map e.symm.toMonoidHom := by
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.symm.surjective]
  rfl

theorem isQuasisimple_map_mulEquiv {H : Type*} [Group H] (e : H ≃* G) {J : Subgroup H}
    (hJ : CFSG.IsQuasisimple J) : CFSG.IsQuasisimple (J.map e.toMonoidHom) :=
  (isQuasisimple_congr (J.equivMapOfInjective e.toMonoidHom e.injective)).1 hJ

theorem isQuasisimple_range_of_ker_le_center {Q H : Type*} [Group Q] [Group H]
    (hQ : CFSG.IsQuasisimple Q) (f : Q →* H) (hf : f.ker ≤ Subgroup.center Q) :
    CFSG.IsQuasisimple f.range := by
  rcases quasisimple_homomorphic_images hQ f with h | h
  · exfalso
    have hcen : ∀ x : Q, x ∈ Subgroup.center Q := fun x => hf (by
      have hx : f x ∈ f.range := ⟨x, rfl⟩
      rw [h, Subgroup.mem_bot] at hx
      exact hx)
    obtain ⟨a, b, hab⟩ := hQ.2.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      Subgroup.mem_center_iff.mp (hcen y) x]
  · exact h

theorem orderOf_ne_of_prime_dvd_card [Finite G]
    (h : ∀ p : ℕ, p.Prime → p ∣ Nat.card G → p = 2 ∨ p = 3) (g : G) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) : orderOf g ≠ p := by
  intro hg
  rcases h p hp (hg ▸ orderOf_dvd_natCard g) with rfl | rfl <;> omega

theorem prime_dvd_forty_eight {p : ℕ} (hp : p.Prime) (h : p ∣ 48) : p = 2 ∨ p = 3 := by
  rw [show (48 : ℕ) = 2 ^ 4 * 3 by norm_num] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)

theorem card_GL_two_dvd_forty_eight {K : Type*} [Field K] [Finite K] (hK : Nat.card K ≤ 3) :
    Nat.card (Matrix.GeneralLinearGroup (Fin 2) K) ∣ 48 := by
  let := Fintype.ofFinite K
  rw [Matrix.card_GL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card]
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rcases (show Nat.card K = 2 ∨ Nat.card K = 3 by omega) with h | h <;> rw [h] <;> norm_num

end CFSG.LocalAnalysis.ComponentInitial
