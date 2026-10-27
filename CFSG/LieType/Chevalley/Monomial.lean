module

public import Mathlib

public section

namespace CFSG.LieType.Chevalley

variable {K V ι Λ W G : Type*} [Field K] [AddCommGroup V] [Module K V] (b : Module.Basis ι K V)
  (wt : ι → Λ) [Group W] [MulAction W Λ] [Group G] (ρ : G →* Module.End K V)

@[expose] def IsMonomial (x : G) (w : W) : Prop :=
  ∀ i j, b.repr (ρ x (b j)) i ≠ 0 → wt i = w • wt j

variable {b wt ρ}

theorem isMonomial_one : IsMonomial b wt ρ 1 (1 : W) := by
  classical
  intro i j h
  rw [map_one, Module.End.one_apply, Module.Basis.repr_self, Finsupp.single_apply] at h
  split_ifs at h with hij
  · rw [hij, one_smul]
  · exact absurd rfl h

theorem IsMonomial.mul {x y : G} {w w' : W} (hx : IsMonomial b wt ρ x w)
    (hy : IsMonomial b wt ρ y w') : IsMonomial b wt ρ (x * y) (w * w') := by
  intro i j h
  rw [map_mul, Module.End.mul_apply] at h
  set c := b.repr (ρ y (b j)) with hc
  have hexp : ρ y (b j) = c.sum fun k a => a • b k := by
    rw [hc, ← Finsupp.linearCombination_apply, Module.Basis.linearCombination_repr]
  rw [hexp, Finsupp.sum, map_sum, map_sum, Finsupp.finsetSum_apply] at h
  obtain ⟨k, hk, hk'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul] at hk'
  have h1 : b.repr (ρ x (b k)) i ≠ 0 := right_ne_zero_of_mul hk'
  rw [hx i k h1, hy k j (Finsupp.mem_support_iff.mp hk), mul_smul]

theorem IsMonomial.pow {x : G} {w : W} (hx : IsMonomial b wt ρ x w) (m : ℕ) :
    IsMonomial b wt ρ (x ^ m) (w ^ m) := by
  induction m with
  | zero => simpa using isMonomial_one
  | succ m ih => rw [pow_succ, pow_succ]; exact ih.mul hx

theorem IsMonomial.unique (hfaith : ∀ w w' : W, (∀ j, w • wt j = w' • wt j) → w = w')
    {x : G} {w w' : W} (hx : IsMonomial b wt ρ x w) (hx' : IsMonomial b wt ρ x w') : w = w' := by
  refine hfaith w w' fun j => ?_
  have hne : ρ x (b j) ≠ 0 := by
    intro h0
    have := congrArg (ρ x⁻¹) h0
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      map_zero] at this
    exact b.ne_zero j this
  obtain ⟨i, hi⟩ : ∃ i, b.repr (ρ x (b j)) i ≠ 0 := by
    by_contra! h
    exact hne (b.repr.injective (by ext i; simpa using h i))
  rw [← hx i j hi, ← hx' i j hi]

variable (b wt ρ W) in
@[expose] def IsMonomialSubgroup (N : Subgroup G) : Prop :=
  ∀ x ∈ N, ∃ w : W, IsMonomial b wt ρ x w

theorem isMonomialSubgroup_closure [Finite G] {S : Set G}
    (hS : ∀ x ∈ S, ∃ w : W, IsMonomial b wt ρ x w) :
    IsMonomialSubgroup W b wt ρ (Subgroup.closure S) := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact ⟨1, isMonomial_one⟩
  | mul x y _ _ hx hy =>
    obtain ⟨w, hw⟩ := hx
    obtain ⟨w', hw'⟩ := hy
    exact ⟨w * w', hw.mul hw'⟩
  | inv x _ hx =>
    obtain ⟨w, hw⟩ := hx
    have hcard : 0 < Nat.card G := Nat.card_pos
    have hpow : x ^ Nat.card G = 1 := pow_card_eq_one'
    have hinv : x⁻¹ = x ^ (Nat.card G - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hcard, hpow]
    rw [hinv]
    exact ⟨_, hw.pow _⟩

variable (b wt ρ) in
@[expose] noncomputable def monomialHom (hfaith : ∀ w w' : W, (∀ j, w • wt j = w' • wt j) → w = w')
    (N : Subgroup G) (hN : IsMonomialSubgroup W b wt ρ N) : N →* W where
  toFun x := Classical.choose (hN x x.2)
  map_one' := (Classical.choose_spec (hN _ (one_mem N))).unique hfaith isMonomial_one
  map_mul' x y := by
    have hxy := Classical.choose_spec (hN _ (mul_mem x.2 y.2))
    have hx := Classical.choose_spec (hN x x.2)
    have hy := Classical.choose_spec (hN y y.2)
    exact hxy.unique hfaith (hx.mul hy)

theorem isMonomial_monomialHom
    (hfaith : ∀ w w' : W, (∀ j, w • wt j = w' • wt j) → w = w') {N : Subgroup G}
    (hN : IsMonomialSubgroup W b wt ρ N) (x : N) :
    IsMonomial b wt ρ (x : G) (monomialHom b wt ρ hfaith N hN x) :=
  Classical.choose_spec (hN x x.2)

theorem monomialHom_eq
    (hfaith : ∀ w w' : W, (∀ j, w • wt j = w' • wt j) → w = w') {N : Subgroup G}
    (hN : IsMonomialSubgroup W b wt ρ N) {x : N} {w : W} (hx : IsMonomial b wt ρ (x : G) w) :
    monomialHom b wt ρ hfaith N hN x = w :=
  (isMonomial_monomialHom hfaith hN x).unique hfaith hx

end CFSG.LieType.Chevalley
