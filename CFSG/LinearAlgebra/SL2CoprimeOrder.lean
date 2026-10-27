module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Polynomial.SpecificDegree

public section

namespace CFSG.LinearAlgebra

open Polynomial

variable {k : Type*} [Field k] [Fintype k]

omit [Fintype k] in
theorem pow_eq_one_of_charpoly_dvd (A : Matrix (Fin 2) (Fin 2) k) {m : ℕ}
    (h : A.charpoly ∣ (X ^ m - 1 : k[X])) : A ^ m = 1 := by
  have h1 := aeval_eq_zero_of_dvd_aeval_eq_zero h (Matrix.aeval_self_charpoly A)
  rw [map_sub, aeval_X_pow, map_one, sub_eq_zero] at h1
  exact h1

omit [Fintype k] in
theorem mul_self_eq_trace_smul_sub_one (A : Matrix (Fin 2) (Fin 2) k) (hA : A.det = 1) :
    A * A = A.trace • A - 1 := by
  have h := Matrix.aeval_self_charpoly A
  rw [Matrix.charpoly_fin_two, hA] at h
  simp only [map_add, map_sub, map_mul, aeval_X_pow, aeval_C, aeval_X, map_one,
    Algebra.algebraMap_eq_smul_one] at h
  rw [← sub_eq_zero, ← h, sq, smul_mul_assoc, one_mul]
  abel

omit [Fintype k] in
theorem charpoly_eq_mul_of_isRoot (A : Matrix (Fin 2) (Fin 2) k) (hA : A.det = 1) {μ : k}
    (hμ : A.charpoly.IsRoot μ) :
    μ ≠ 0 ∧ A.trace = μ + μ⁻¹ ∧ A.charpoly = (X - C μ) * (X - C μ⁻¹) := by
  have hev : μ ^ 2 - A.trace * μ + 1 = 0 := by
    have h := hμ
    rw [IsRoot.def, Matrix.charpoly_fin_two, hA] at h
    simpa using h
  have hμ0 : μ ≠ 0 := fun h => by
    rw [h] at hev
    simp at hev
  have hs : A.trace = μ + μ⁻¹ := by
    field_simp
    linear_combination -hev
  refine ⟨hμ0, hs, ?_⟩
  have hC : C μ * C μ⁻¹ = (1 : k[X]) := by
    rw [← C_mul, mul_inv_cancel₀ hμ0, C_1]
  rw [Matrix.charpoly_fin_two, hA, hs, C_add, C_1]
  linear_combination -hC

omit [Fintype k] in
theorem pow_succ_of_sq_eq (A : Matrix (Fin 2) (Fin 2) k) {μ : k}
    (hA2 : A * A = (2 * μ) • A - (μ ^ 2) • (1 : Matrix (Fin 2) (Fin 2) k)) (m : ℕ) :
    A ^ (m + 1) = (((m : k) + 1) * μ ^ m) • A -
      ((m : k) * μ ^ (m + 1)) • (1 : Matrix (Fin 2) (Fin 2) k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul, hA2, smul_sub,
      smul_smul, smul_smul]
    push_cast
    module

theorem pow_card_sub_one_or_pow_card_add_one (A : Matrix (Fin 2) (Fin 2) k) (hA : A.det = 1)
    {n : ℕ} (hn : A ^ n = 1) (hnk : (n : k) ≠ 0) :
    A ^ (Fintype.card k - 1) = 1 ∨ A ^ (Fintype.card k + 1) = 1 := by
  classical
  by_cases hroot : ∃ μ : k, A.charpoly.IsRoot μ
  ·
    left
    obtain ⟨μ, hμ⟩ := hroot
    obtain ⟨hμ0, hs, hχ⟩ := charpoly_eq_mul_of_isRoot A hA hμ
    by_cases hne : μ ≠ μ⁻¹
    · apply pow_eq_one_of_charpoly_dvd
      rw [hχ]
      apply IsCoprime.mul_dvd (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hne).isUnit)
      · rw [dvd_iff_isRoot, IsRoot.def, eval_sub, eval_pow, eval_X, eval_one,
          FiniteField.pow_card_sub_one_eq_one μ hμ0, sub_self]
      · rw [dvd_iff_isRoot, IsRoot.def, eval_sub, eval_pow, eval_X, eval_one,
          FiniteField.pow_card_sub_one_eq_one μ⁻¹ (inv_ne_zero hμ0), sub_self]
    ·
      have hne' : μ = μ⁻¹ := not_not.mp hne
      have hsq : μ ^ 2 = 1 := by
        rw [sq]
        nth_rewrite 2 [hne']
        exact mul_inv_cancel₀ hμ0
      have hA2 : A * A = (2 * μ) • A - (μ ^ 2) • (1 : Matrix (Fin 2) (Fin 2) k) := by
        rw [mul_self_eq_trace_smul_sub_one A hA, hs, ← hne', hsq, one_smul, two_mul]
      have hn0 : n ≠ 0 := fun h => hnk (by rw [h, Nat.cast_zero])
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      have hpow := pow_succ_of_sq_eq A hA2 m
      rw [hn] at hpow
      have hcoef : ((m : k) + 1) * μ ^ m ≠ 0 := by
        refine mul_ne_zero ?_ (pow_ne_zero _ hμ0)
        simpa [Nat.cast_succ] using hnk
      set c : k := (((m : k) + 1) * μ ^ m)⁻¹ * (1 + (m : k) * μ ^ (m + 1)) with hcdef
      have hAc : A = c • (1 : Matrix (Fin 2) (Fin 2) k) := by
        have h1 : (((m : k) + 1) * μ ^ m) • A =
            (1 + (m : k) * μ ^ (m + 1)) • (1 : Matrix (Fin 2) (Fin 2) k) := by
          have h2 := hpow
          rw [eq_sub_iff_add_eq] at h2
          rw [← h2, add_smul, one_smul]
        rw [hcdef, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hcoef, one_smul]
      have hc0 : c ≠ 0 := by
        intro h0
        rw [hAc, h0, zero_smul, Matrix.det_zero] at hA
        exact zero_ne_one hA
      rw [hAc, smul_pow, one_pow, FiniteField.pow_card_sub_one_eq_one c hc0, one_smul]
  ·
    right
    replace hroot := not_exists.mp hroot
    have hdeg : A.charpoly.natDegree = 2 := by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    have hirr : Irreducible A.charpoly :=
      irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) hroot
    have : Fact (Irreducible A.charpoly) := ⟨hirr⟩
    apply pow_eq_one_of_charpoly_dvd
    rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq, map_sub, aeval_X_pow, map_one,
      sub_eq_zero]
    set θ := AdjoinRoot.root A.charpoly with hθ
    set q := Fintype.card k with hq
    have hfrob : ∀ g : k[X], (aeval θ g) ^ q = aeval (θ ^ q) g := fun g => by
      rw [← expand_aeval, hq, FiniteField.Polynomial.expand_card, map_pow]
    have hθroot : aeval θ A.charpoly = 0 := by
      rw [hθ, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    have hθq : aeval (θ ^ q) A.charpoly = 0 := by
      rw [← hfrob, hθroot, zero_pow (by rw [hq]; exact Fintype.card_ne_zero)]
    have hθk : θ ∉ Set.range (algebraMap k (AdjoinRoot A.charpoly)) := by
      rintro ⟨c, hc⟩
      apply hroot c
      have h := hθroot
      rw [← hc, aeval_algebraMap_apply, coe_aeval_eq_eval] at h
      exact (map_eq_zero_iff _ (algebraMap k (AdjoinRoot A.charpoly)).injective).mp h
    have hθqne : θ ^ q ≠ θ := by
      intro hfix
      have hall : ∀ x : AdjoinRoot A.charpoly, x ^ q = x := by
        intro x
        obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
        rw [← AdjoinRoot.aeval_eq, hfrob, hfix]
      have hq1 : 1 < q := by rw [hq]; exact Fintype.one_lt_card
      have hP0 : (X ^ q - X : (AdjoinRoot A.charpoly)[X]) ≠ 0 := by
        intro h
        have h1 := FiniteField.X_pow_card_sub_X_natDegree_eq (AdjoinRoot A.charpoly) hq1
        rw [h, natDegree_zero] at h1
        omega
      have hmem : ∀ x : AdjoinRoot A.charpoly,
          x ∈ (X ^ q - X : (AdjoinRoot A.charpoly)[X]).roots.toFinset := by
        intro x
        rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot.def, eval_sub, eval_pow, eval_X,
          hall x, sub_self]
      have hsub : insert θ (Finset.univ.map ⟨algebraMap k (AdjoinRoot A.charpoly),
          (algebraMap k (AdjoinRoot A.charpoly)).injective⟩) ⊆
          (X ^ q - X : (AdjoinRoot A.charpoly)[X]).roots.toFinset := fun x _ => hmem x
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
          rintro ⟨c, hc⟩
          exact hθk ⟨c, hc⟩), Finset.card_map, Finset.card_univ, ← hq] at hcard
      have h2 := (Multiset.toFinset_card_le _).trans (card_roots'
        (X ^ q - X : (AdjoinRoot A.charpoly)[X]))
      rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ hq1] at h2
      omega
    have hχ' : A.charpoly = X ^ 2 - C A.trace * X + 1 := by
      rw [Matrix.charpoly_fin_two, hA, C_1]
    have heval : ∀ x : AdjoinRoot A.charpoly, aeval x A.charpoly =
        x ^ 2 - algebraMap k _ A.trace * x + 1 := by
      intro x
      rw [congrArg (aeval x) hχ']
      simp only [map_add, map_sub, map_mul, aeval_X_pow, aeval_C, aeval_X, map_one]
    have hvieta : ∀ x : AdjoinRoot A.charpoly, aeval x A.charpoly =
        (x - θ) * (x - (algebraMap k _ A.trace - θ)) := by
      intro x
      have h := hθroot
      rw [heval] at h
      rw [heval]
      linear_combination h
    have hθq' : θ ^ q = algebraMap k _ A.trace - θ := by
      rw [hvieta] at hθq
      rcases mul_eq_zero.mp hθq with h | h
      · exact absurd (sub_eq_zero.mp h) hθqne
      · exact sub_eq_zero.mp h
    have h := hθroot
    rw [heval] at h
    rw [pow_succ, hθq']
    linear_combination -h

theorem finite_field_SL2_coprime_cyclic_order {K : Type*} [Field K] [Finite K] (p : ℕ)
    [CharP K p] :
    (∀ A : Matrix (Fin 2) (Fin 2) K, A.det = 1 → Nat.Coprime (orderOf A) p →
      orderOf A ∣ Nat.card K - 1 ∨ orderOf A ∣ Nat.card K + 1) ∧
    (∀ C : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K), IsCyclic C →
      Nat.Coprime (Nat.card C) p → Nat.card C ∣ Nat.card K - 1 ∨ Nat.card C ∣ Nat.card K + 1) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hp : p.Prime := CharP.char_is_prime K p
  have hmatrix : ∀ A : Matrix (Fin 2) (Fin 2) K, A.det = 1 → Nat.Coprime (orderOf A) p →
      orderOf A ∣ Nat.card K - 1 ∨ orderOf A ∣ Nat.card K + 1 := by
    intro A hA hcop
    have hn0 : orderOf A ≠ 0 := by
      intro h
      rw [h, Nat.coprime_zero_left] at hcop
      exact hp.one_lt.ne' hcop
    have hnk : ((orderOf A : ℕ) : K) ≠ 0 := by
      rw [ne_eq, CharP.cast_eq_zero_iff K p]
      intro hdvd
      have := Nat.Coprime.coprime_dvd_left hdvd hcop
      rw [Nat.coprime_self] at this
      exact hp.one_lt.ne' this
    rw [Nat.card_eq_fintype_card]
    rcases pow_card_sub_one_or_pow_card_add_one A hA (pow_orderOf_eq_one A) hnk with h | h
    · exact Or.inl (orderOf_dvd_of_pow_eq_one h)
    · exact Or.inr (orderOf_dvd_of_pow_eq_one h)
  refine ⟨hmatrix, fun C hC hcop => ?_⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  have hcard : orderOf g = Nat.card C := orderOf_eq_card_of_forall_mem_zpowers hg
  have horder : orderOf (((g : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K)) = orderOf g := by
    rw [← Subgroup.orderOf_coe, orderOf_eq_orderOf_iff]
    intro m
    rw [← Matrix.SpecialLinearGroup.coe_pow]
    constructor
    · intro h
      exact Matrix.SpecialLinearGroup.ext _ _ fun i j => by rw [h]; rfl
    · intro h
      rw [h]
      rfl
  rw [← hcard, ← horder]
  exact hmatrix _ (Matrix.SpecialLinearGroup.det_coe _) (by rw [horder, hcard]; exact hcop)

end CFSG.LinearAlgebra
