module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.FieldTheory.IsAlgClosed.Basic

public section

namespace CFSG.LieType.Chevalley.E7Three.HeisenbergPair

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

section Basis

variable {ω : K} {T S : Module.End K V}

theorem one_add_add_sq (hω : IsPrimitiveRoot ω 3) : 1 + ω + ω ^ 2 = 0 := by
  have h := hω.geom_sum_eq_zero (by norm_num)
  simpa [Finset.sum_range_succ] using h

theorem eq_zero_of_add_eq_zero (hω : IsPrimitiveRoot ω 3) (h3 : (3 : K) ≠ 0) {w₀ w₁ w₂ : V}
    (hw₀ : T w₀ = w₀) (hw₁ : T w₁ = ω • w₁) (hw₂ : T w₂ = ω ^ 2 • w₂)
    (h : w₀ + w₁ + w₂ = 0) : w₀ = 0 ∧ w₁ = 0 ∧ w₂ = 0 := by
  have hs := one_add_add_sq hω
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have e3 : ω ^ 2 * ω = 1 := by rw [← pow_succ, hω3]
  have e3' : ω * ω ^ 2 = 1 := by rw [← pow_succ', hω3]
  have e4 : ω ^ 2 * ω ^ 2 = ω := by
    calc ω ^ 2 * ω ^ 2 = ω ^ 3 * ω := by ring
      _ = ω := by rw [hω3, one_mul]
  have e2 : ω * ω = ω ^ 2 := by ring
  have h1 : w₀ + ω • w₁ + ω ^ 2 • w₂ = 0 := by
    have := congrArg T h
    rwa [map_add, map_add, hw₀, hw₁, hw₂, map_zero] at this
  have h2 : w₀ + ω ^ 2 • w₁ + ω • w₂ = 0 := by
    have := congrArg T h1
    rwa [map_add, map_add, map_smul, map_smul, hw₀, hw₁, hw₂, map_zero, smul_smul, smul_smul,
      e2, e4] at this
  have h1' : ω ^ 2 • w₀ + w₁ + ω • w₂ = 0 := by
    have := congrArg (fun v => ω ^ 2 • v) h1
    simpa only [smul_add, smul_smul, e3, e4, one_smul, smul_zero] using this
  have h2' : ω • w₀ + w₁ + ω ^ 2 • w₂ = 0 := by
    have := congrArg (fun v => ω • v) h2
    simpa only [smul_add, smul_smul, e3', e2, one_smul, smul_zero] using this
  have k₀ : (3 : K) • w₀ = 0 := by
    have e : (3 : K) • w₀ = (w₀ + w₁ + w₂) + (w₀ + ω • w₁ + ω ^ 2 • w₂) +
        (w₀ + ω ^ 2 • w₁ + ω • w₂) - (1 + ω + ω ^ 2) • (w₁ + w₂) := by module
    rw [e, h, h1, h2, hs]; simp
  have k₁ : (3 : K) • w₁ = 0 := by
    have e : (3 : K) • w₁ = (w₀ + w₁ + w₂) + (ω ^ 2 • w₀ + w₁ + ω • w₂) +
        (ω • w₀ + w₁ + ω ^ 2 • w₂) - (1 + ω + ω ^ 2) • (w₀ + w₂) := by module
    rw [e, h, h1', h2', hs]; simp
  have k₂ : (3 : K) • w₂ = 0 := by
    have h1'' : ω • w₀ + ω ^ 2 • w₁ + w₂ = 0 := by
      have := congrArg (fun v => ω • v) h1
      simpa only [smul_add, smul_smul, e3', e2, one_smul, smul_zero] using this
    have h2'' : ω ^ 2 • w₀ + ω • w₁ + w₂ = 0 := by
      have := congrArg (fun v => ω ^ 2 • v) h2
      simpa only [smul_add, smul_smul, e3, e4, one_smul, smul_zero] using this
    have e : (3 : K) • w₂ = (w₀ + w₁ + w₂) + (ω • w₀ + ω ^ 2 • w₁ + w₂) +
        (ω ^ 2 • w₀ + ω • w₁ + w₂) - (1 + ω + ω ^ 2) • (w₀ + w₁) := by module
    rw [e, h, h1'', h2'', hs]; simp
  exact ⟨(smul_eq_zero.1 k₀).resolve_left h3, (smul_eq_zero.1 k₁).resolve_left h3,
    (smul_eq_zero.1 k₂).resolve_left h3⟩

theorem apply_pow_of_eigen (hTS : T * S = ω • (S * T)) {u : V} {m : ℕ} (hu : T u = ω ^ m • u)
    (j : ℕ) : T ((S ^ j) u) = ω ^ (m + j) • (S ^ j) u := by
  induction j with
  | zero => simpa using hu
  | succ j ih =>
    calc T ((S ^ (j + 1)) u) = (T * S) ((S ^ j) u) := by rw [pow_succ']; rfl
      _ = ω • S (T ((S ^ j) u)) := by rw [hTS]; rfl
      _ = ω ^ (m + (j + 1)) • (S ^ (j + 1)) u := by
        rw [ih, map_smul, smul_smul, ← pow_succ', pow_succ' S, ← add_assoc]; rfl

variable [FiniteDimensional K V]

theorem exists_basis_heis (hω : IsPrimitiveRoot ω 3) (h3 : (3 : K) ≠ 0)
    (hTS : T * S = ω • (S * T)) (hT : T ^ 3 = 1) (hS : S ^ 3 = 1) :
    ∃ (d : ℕ) (f : Basis (Fin d × Fin 3) K V),
      (∀ i j, T (f (i, j)) = ω ^ (j : ℕ) • f (i, j)) ∧ ∀ i j, S (f (i, j)) = f (i, j + 1) := by
  classical
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hs := one_add_add_sq hω
  set E₀ : Submodule K V := LinearMap.ker (T - 1) with hE₀
  have hmem : ∀ u : V, u ∈ E₀ ↔ T u = u := by
    intro u
    simp [E₀, sub_eq_zero]
  let b := Module.finBasis K E₀
  let f : Fin (finrank K E₀) × Fin 3 → V := fun p => (S ^ (p.2 : ℕ)) (b p.1 : V)
  have hTf : ∀ p, T (f p) = ω ^ (p.2 : ℕ) • f p := fun p => by
    have := apply_pow_of_eigen (m := 0) hTS (by simpa using (hmem _).1 (b p.1).2) (p.2 : ℕ)
    simpa only [zero_add] using this
  have hS3 : ∀ x : V, (S ^ 3) x = x := fun x => by rw [hS]; rfl
  have hSf : ∀ i j, S (f (i, j)) = f (i, j + 1) := by
    intro i j
    fin_cases j
    · change S ((S ^ 0) (b i : V)) = (S ^ 1) (b i : V)
      rw [pow_zero, pow_one]; rfl
    · change S ((S ^ 1) (b i : V)) = (S ^ 2) (b i : V)
      rw [pow_one, pow_two]; rfl
    · change S ((S ^ 2) (b i : V)) = (S ^ 0) (b i : V)
      have e : S ((S ^ 2) (b i : V)) = (S ^ 3) (b i : V) := by rw [pow_succ' S 2]; rfl
      rw [e, hS3, pow_zero]; rfl
  have hSinj : ∀ j : ℕ, Function.Injective (S ^ j) := by
    intro j x y hxy
    have h' : (S ^ (3 * j)) x = (S ^ (3 * j)) y := by
      rw [show 3 * j = 2 * j + j by ring, pow_add]
      exact congrArg (S ^ (2 * j)) hxy
    rwa [pow_mul, hS, one_pow] at h'
  have hli : LinearIndependent K f := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    set w : Fin 3 → V := fun j => ∑ i, g (i, j) • f (i, j) with hw
    have hsum : w 0 + w 1 + w 2 = 0 := by
      rw [← hg, Fintype.sum_prod_type_right, Fin.sum_univ_three]
    have hTw : ∀ j, T (w j) = ω ^ (j : ℕ) • w j := by
      intro j
      simp only [hw, map_sum, map_smul, hTf, Finset.smul_sum, smul_comm (g _) (ω ^ _)]
    obtain ⟨h0, h1, h2⟩ := eq_zero_of_add_eq_zero hω h3 (by simpa using hTw 0)
      (by simpa using hTw 1) (by simpa using hTw 2) hsum
    have hwj : ∀ j, w j = 0 := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    intro ⟨i, j⟩
    have hE : (∑ i, g (i, j) • b i : E₀) = 0 := by
      apply Subtype.ext
      apply hSinj (j : ℕ)
      have := hwj j
      simp only [hw, f] at this
      simpa [map_sum, map_smul] using this
    exact (Fintype.linearIndependent_iff.1 b.linearIndependent (fun i => g (i, j)) hE) i
  have hspan : ⊤ ≤ Submodule.span K (Set.range f) := by
    have hcol : ∀ (j : Fin 3) (u : V), T u = ω ^ (j : ℕ) • u →
        u ∈ Submodule.span K (Set.range f) := by
      intro j u hu
      set u₀ := (S ^ (3 - (j : ℕ))) u with hu₀
      have hT0 : T u₀ = u₀ := by
        have := apply_pow_of_eigen hTS hu (3 - (j : ℕ))
        rwa [show (j : ℕ) + (3 - (j : ℕ)) = 3 by omega, hω3, one_smul] at this
      have huu : u = (S ^ (j : ℕ)) u₀ := by
        rw [hu₀, ← Module.End.mul_apply, ← pow_add, show (j : ℕ) + (3 - (j : ℕ)) = 3 by omega,
          hS]; rfl
      have hrepr := b.sum_repr ⟨u₀, (hmem u₀).2 hT0⟩
      rw [huu]
      have : u₀ = ∑ i, b.repr ⟨u₀, (hmem u₀).2 hT0⟩ i • (b i : V) := by
        have h' := congrArg Subtype.val hrepr
        rw [Submodule.coe_sum] at h'
        exact h'.symm
      rw [this, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
    intro v _
    set c₀ := (3 : K)⁻¹ • (v + T v + (T ^ 2) v)
    set c₁ := (3 : K)⁻¹ • (v + ω ^ 2 • T v + ω • (T ^ 2) v)
    set c₂ := (3 : K)⁻¹ • (v + ω • T v + ω ^ 2 • (T ^ 2) v)
    have hT3 : (T ^ 3) v = v := by rw [hT]; rfl
    have hTT : ∀ x : V, T ((T ^ 2) x) = (T ^ 3) x := fun x => by rw [pow_succ' T 2]; rfl
    have hTT' : ∀ x : V, T (T x) = (T ^ 2) x := fun x => by rw [pow_two]; rfl
    have hc₀ : T c₀ = ω ^ ((0 : Fin 3) : ℕ) • c₀ := by
      have hTc : T c₀ = (3 : K)⁻¹ • (T v + (T ^ 2) v + v) := by
        simp only [c₀, map_smul, map_add, hTT, hTT', hT3]
      rw [hTc, Fin.val_zero, pow_zero, one_smul]
      simp only [c₀]
      module
    have hc₁ : T c₁ = ω ^ ((1 : Fin 3) : ℕ) • c₁ := by
      have hTc : T c₁ = (3 : K)⁻¹ • (T v + ω ^ 2 • (T ^ 2) v + ω • v) := by
        simp only [c₁, map_smul, map_add, hTT, hTT', hT3]
      rw [hTc, Fin.val_one, pow_one]
      simp only [c₁]
      linear_combination (norm := module) hω3 • (-(3 : K)⁻¹ • T v)
    have hc₂ : T c₂ = ω ^ ((2 : Fin 3) : ℕ) • c₂ := by
      have hTc : T c₂ = (3 : K)⁻¹ • (T v + ω • (T ^ 2) v + ω ^ 2 • v) := by
        simp only [c₂, map_smul, map_add, hTT, hTT', hT3]
      rw [hTc, Fin.val_two]
      simp only [c₂]
      linear_combination (norm := module) hω3 • (-(3 : K)⁻¹ • (T v + ω • (T ^ 2) v))
    have hv : v = c₀ + c₁ + c₂ := by
      have e : v = (3 : K)⁻¹ • ((3 : K) • v + (1 + ω ^ 2 + ω) • T v +
          (1 + ω + ω ^ 2) • (T ^ 2) v) := by
        rw [show 1 + ω ^ 2 + ω = 1 + ω + ω ^ 2 by ring, hs, zero_smul, zero_smul, add_zero,
          add_zero, smul_smul, inv_mul_cancel₀ h3, one_smul]
      rw [e]
      simp only [c₀, c₁, c₂]
      module
    rw [hv]
    exact Submodule.add_mem _ (Submodule.add_mem _ (hcol 0 _ hc₀) (hcol 1 _ hc₁)) (hcol 2 _ hc₂)
  refine ⟨finrank K E₀, Basis.mk hli hspan, fun i j => ?_, fun i j => ?_⟩
  · rw [Basis.mk_apply]
    exact hTf (i, j)
  · rw [Basis.mk_apply, Basis.mk_apply]
    exact hSf i j

end Basis

section Matrices

open Matrix
open scoped Kronecker

@[expose] def shift3 : Matrix (Fin 3) (Fin 3) K := fun j j' => if j = j' + 1 then 1 else 0

theorem exists_mul_eq_heis {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
    (e : ι × Fin 3 ≃ n) {ω : K} (hω : IsPrimitiveRoot ω 3) (h3 : (3 : K) ≠ 0)
    {A B : Matrix n n K} (hAB : A * B = ω • (B * A)) (hA : A ^ 3 = 1) (hB : B ^ 3 = 1) :
    ∃ Q : Matrix n n K, IsUnit Q.det ∧
      A * Q = Q * reindex e e ((1 : Matrix ι ι K) ⊗ₖ diagonal fun j : Fin 3 => ω ^ (j : ℕ)) ∧
      B * Q = Q * reindex e e ((1 : Matrix ι ι K) ⊗ₖ shift3) := by
  classical
  let T : Module.End K (n → K) := Matrix.toLinAlgEquiv' A
  let S : Module.End K (n → K) := Matrix.toLinAlgEquiv' B
  have hTS : T * S = ω • (S * T) := by
    simp only [T, S, ← map_mul, ← map_smul, hAB]
  have hT : T ^ 3 = 1 := by simp only [T, ← map_pow, hA, map_one]
  have hS : S ^ 3 = 1 := by simp only [S, ← map_pow, hB, map_one]
  obtain ⟨d, f, hTf, hSf⟩ := exists_basis_heis hω h3 hTS hT hS
  have hcard : Fintype.card (Fin d) = Fintype.card ι := by
    have h1 := Module.finrank_eq_card_basis f
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_congr e.symm, Fintype.card_prod,
      Fintype.card_prod] at h1
    exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h1).symm
  let σ : Fin d ≃ ι := Fintype.equivOfCardEq hcard
  let f' : Basis n K (n → K) := f.reindex ((σ.prodCongr (Equiv.refl _)).trans e)
  have hf' : ∀ i j, f' (e (i, j)) = f (σ.symm i, j) := by
    intro i j
    simp [f', Basis.reindex_apply]
  let Q : Matrix n n K := (Pi.basisFun K n).toMatrix f'
  have hQ : ∀ x y, Q x y = f' y x := by
    intro x y
    simp [Q, Basis.toMatrix_apply]
  have hQu : IsUnit Q.det := by
    have := Basis.invertibleToMatrix (Pi.basisFun K n) f'
    exact Matrix.isUnit_det_of_invertible Q
  refine ⟨Q, hQu, ?_, ?_⟩
  · ext x y
    obtain ⟨⟨i, j⟩, rfl⟩ := e.surjective y
    have hT' := congrFun (hTf (σ.symm i) j) x
    rw [← hf'] at hT'
    have hl : (A * Q) x (e (i, j)) = T (f' (e (i, j))) x := by
      simp only [T, Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply, Matrix.mul_apply,
        Matrix.mulVec, dotProduct, hQ]
    rw [hl, hT', Matrix.mul_apply]
    rw [Finset.sum_eq_single (e (i, j))]
    · simp [hQ, reindex_apply, kroneckerMap_apply, mul_comm]
    · intro z _ hz
      obtain ⟨⟨i', j'⟩, rfl⟩ := e.surjective z
      simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, kroneckerMap_apply,
        Matrix.one_apply, diagonal_apply]
      have : ¬ (i' = i ∧ j' = j) := fun h => hz (by rw [h.1, h.2])
      by_cases hi : i' = i
      · have hj : j' ≠ j := fun hj => this ⟨hi, hj⟩
        simp [hi, hj]
      · simp [hi]
    · simp
  · ext x y
    obtain ⟨⟨i, j⟩, rfl⟩ := e.surjective y
    have hS' := congrFun (hSf (σ.symm i) j) x
    rw [← hf', ← hf'] at hS'
    have hl : (B * Q) x (e (i, j)) = S (f' (e (i, j))) x := by
      simp only [S, Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply, Matrix.mul_apply,
        Matrix.mulVec, dotProduct, hQ]
    rw [hl, hS', Matrix.mul_apply]
    rw [Finset.sum_eq_single (e (i, j + 1))]
    · simp [hQ, reindex_apply, kroneckerMap_apply, shift3]
    · intro z _ hz
      obtain ⟨⟨i', j'⟩, rfl⟩ := e.surjective z
      simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, kroneckerMap_apply,
        Matrix.one_apply, shift3]
      have : ¬ (i' = i ∧ j' = j + 1) := fun h => hz (by rw [h.1, h.2])
      by_cases hi : i' = i
      · have hj : j' ≠ j + 1 := fun hj => this ⟨hi, hj⟩
        simp [hi, hj]
      · simp [hi]
    · simp

theorem exists_sl_conj_eq [IsAlgClosed K] {n : Type*} [Fintype n] [DecidableEq n]
    {Q : Matrix n n K} (hQ : IsUnit Q.det) :
    ∃ P : Matrix.SpecialLinearGroup n K, ∀ X : Matrix.SpecialLinearGroup n K,
      ((P * X * P⁻¹ : Matrix.SpecialLinearGroup n K) : Matrix n n K) = Q⁻¹ * X * Q := by
  classical
  obtain ⟨t, ht0, ht⟩ : ∃ t : K, t ≠ 0 ∧ t ^ Fintype.card n = Q.det := by
    rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | hpos
    · refine ⟨1, one_ne_zero, ?_⟩
      have : IsEmpty n := Fintype.card_eq_zero_iff.1 h0
      rw [h0, pow_zero, Matrix.det_isEmpty]
    · obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq Q.det hpos
      refine ⟨t, ?_, ht⟩
      rintro rfl
      rw [zero_pow hpos.ne'] at ht
      exact hQ.ne_zero ht.symm
  set P₀ : Matrix n n K := t • Q⁻¹ with hP₀
  have hdet : P₀.det = 1 := by
    rw [hP₀, Matrix.det_smul, Matrix.det_nonsing_inv, ht, Ring.mul_inverse_cancel _ hQ]
  have hinv : (Matrix.adjugate P₀ : Matrix n n K) = t⁻¹ • Q := by
    have h1 : P₀⁻¹ = Matrix.adjugate P₀ := by
      rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
    rw [← h1, hP₀]
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ht0, one_smul,
      Matrix.mul_nonsing_inv _ hQ]
  let P : Matrix.SpecialLinearGroup n K := ⟨P₀, hdet⟩
  refine ⟨P, fun X => ?_⟩
  change P₀ * (X : Matrix n n K) * Matrix.adjugate P₀ = _
  rw [hinv, hP₀, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, smul_smul,
    inv_mul_cancel₀ ht0, one_smul]

theorem exists_sl_conj_heis [IsAlgClosed K] {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    [DecidableEq ι] (e : ι × Fin 3 ≃ n) {ω : K} (hω : IsPrimitiveRoot ω 3) (h3 : (3 : K) ≠ 0)
    (A B : Matrix.SpecialLinearGroup n K)
    (hAB : (A : Matrix n n K) * B = ω • ((B : Matrix n n K) * A)) {α β : K} (hα : α ≠ 0)
    (hβ : β ≠ 0) (hA : (A : Matrix n n K) ^ 3 = α • 1) (hB : (B : Matrix n n K) ^ 3 = β • 1) :
    ∃ (P : Matrix.SpecialLinearGroup n K) (c d : K), c ^ 3 = α ∧ d ^ 3 = β ∧
      ((P * A * P⁻¹ : Matrix.SpecialLinearGroup n K) : Matrix n n K) =
        c • reindex e e ((1 : Matrix ι ι K) ⊗ₖ diagonal fun j : Fin 3 => ω ^ (j : ℕ)) ∧
      ((P * B * P⁻¹ : Matrix.SpecialLinearGroup n K) : Matrix n n K) =
        d • reindex e e ((1 : Matrix ι ι K) ⊗ₖ shift3) := by
  classical
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq α (by norm_num : 0 < 3)
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq β (by norm_num : 0 < 3)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hα (by rw [← hc]; ring)
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hβ (by rw [← hd]; ring)
  set A' : Matrix n n K := c⁻¹ • (A : Matrix n n K) with hA'def
  set B' : Matrix n n K := d⁻¹ • (B : Matrix n n K) with hB'def
  have hA' : A' ^ 3 = 1 := by
    rw [hA'def, smul_pow, hA, smul_smul, inv_pow, hc, inv_mul_cancel₀ hα, one_smul]
  have hB' : B' ^ 3 = 1 := by
    rw [hB'def, smul_pow, hB, smul_smul, inv_pow, hd, inv_mul_cancel₀ hβ, one_smul]
  have hAB' : A' * B' = ω • (B' * A') := by
    rw [hA'def, hB'def, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, hAB,
      smul_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  obtain ⟨Q, hQu, hAQ, hBQ⟩ := exists_mul_eq_heis e hω h3 hAB' hA' hB'
  obtain ⟨P, hP⟩ := exists_sl_conj_eq hQu
  have hQQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hQu
  refine ⟨P, c, d, hc, hd, ?_, ?_⟩
  · rw [hP, show (A : Matrix n n K) = c • A' by
      rw [hA'def, smul_smul, mul_inv_cancel₀ hc0, one_smul], Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc, hAQ, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]
  · rw [hP, show (B : Matrix n n K) = d • B' by
      rw [hB'def, smul_smul, mul_inv_cancel₀ hd0, one_smul], Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc, hBQ, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]

end Matrices

end CFSG.LieType.Chevalley.E7Three.HeisenbergPair
