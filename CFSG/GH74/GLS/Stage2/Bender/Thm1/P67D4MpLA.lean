module

public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Matrix

private theorem la_exists_perm_of_columns {L : Type} [Field L] (U : Matrix (Fin 3) (Fin 3) L)
    (hU : U.det ≠ 0) (hcol : ∀ j, ∃ k, U k j ≠ 0 ∧ ∀ a, a ≠ k → U a j = 0) :
    ∃ p : Equiv.Perm (Fin 3), ∀ j, U (p j) j ≠ 0 ∧ ∀ a, a ≠ p j → U a j = 0 := by
  choose f hf0 hf1 using hcol
  have hv : ∀ (j j' r : Fin 3) (a b : L),
      (U *ᵥ (Pi.single j b - Pi.single j' a)) r = U r j * b - U r j' * a := by
    intro j j' r a b
    simp only [Matrix.mulVec_sub, Matrix.mulVec_single, Pi.sub_apply]
    simp
  have hinj : Function.Injective f := by
    intro j j' hjj'
    by_contra hne
    apply hU
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨Pi.single j (U (f j') j') - Pi.single j' (U (f j) j), ?_, ?_⟩
    · intro h0
      have := congrFun h0 j
      simp [hne, hf0 j'] at this
    · ext r
      rw [hv, Pi.zero_apply]
      by_cases hr : r = f j
      · subst hr
        rw [hjj']
        ring
      · have h2 : r ≠ f j' := fun h => hr (h.trans hjj'.symm)
        rw [hf1 j r hr, hf1 j' r h2]
        simp
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj),
    fun j => ⟨hf0 j, hf1 j⟩⟩

private theorem la_perm_values (p : Equiv.Perm (Fin 3)) :
    (p 0 = 0 ∧ p 1 = 1 ∧ p 2 = 2) ∨ (p 0 = 1 ∧ p 1 = 0 ∧ p 2 = 2) ∨
    (p 0 = 0 ∧ p 1 = 2 ∧ p 2 = 1) ∨ (p 0 = 1 ∧ p 1 = 2 ∧ p 2 = 0) ∨
    (p 0 = 2 ∧ p 1 = 0 ∧ p 2 = 1) ∨ (p 0 = 2 ∧ p 1 = 1 ∧ p 2 = 0) := by
  have h01 : p 0 ≠ p 1 := fun h => absurd (p.injective h) (by decide)
  have h02 : p 0 ≠ p 2 := fun h => absurd (p.injective h) (by decide)
  have h12 : p 1 ≠ p 2 := fun h => absurd (p.injective h) (by decide)
  generalize p 0 = a at h01 h02 ⊢
  generalize p 1 = b at h01 h12 ⊢
  generalize p 2 = c at h02 h12 ⊢
  revert a b c
  decide

theorem la_scalar_of_comm_transvections {L : Type} [Field L] (M : Matrix (Fin 3) (Fin 3) L)
    (h : ∀ i j : Fin 3, i ≠ j → M * (1 + Matrix.single i j (1 : L)) =
      (1 + Matrix.single i j (1 : L)) * M) : ∃ r : L, M = r • (1 : Matrix (Fin 3) (Fin 3) L) := by
  have hc : Pairwise fun i j : Fin 3 => Commute (Matrix.single i j (1 : L)) M := by
    intro i j hij
    have := h i j hij
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      add_right_inj] at this
    exact this.symm
  obtain ⟨r, hr⟩ := Matrix.mem_range_scalar_of_commute_single hc
  exact ⟨r, by rw [← hr, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

theorem la_monomial_of_regular_conj {L : Type} [Field L] (d d' : Fin 3 → L)
    (hd' : ∀ i j : Fin 3, i ≠ j → d' i ≠ d' j)
    (U : Matrix (Fin 3) (Fin 3) L) (hU : U.det ≠ 0) (c : L) (hc : c ≠ 0)
    (h : U * Matrix.diagonal d = c • (Matrix.diagonal d' * U)) :
    ∃ p : Equiv.Perm (Fin 3), (∀ i j : Fin 3, U i j ≠ 0 → i = p j) ∧
      ∀ j : Fin 3, d j = c * d' (p j) := by
  have hent : ∀ i j, U i j * d j = c * (d' i * U i j) := by
    intro i j
    have := congrFun (congrFun h i) j
    simpa [Matrix.mul_diagonal, Matrix.smul_apply, Matrix.diagonal_mul] using this
  have hrel : ∀ i j, U i j ≠ 0 → d j = c * d' i := by
    intro i j hij
    apply mul_left_cancel₀ hij
    linear_combination hent i j
  have hcol : ∀ j, ∃ k, U k j ≠ 0 ∧ ∀ a, a ≠ k → U a j = 0 := by
    intro j
    have hex : ∃ k, U k j ≠ 0 := by
      by_contra hno
      exact hU (Matrix.det_eq_zero_of_column_eq_zero j fun a => by
        by_contra ha
        exact hno ⟨a, ha⟩)
    obtain ⟨k, hk⟩ := hex
    refine ⟨k, hk, fun a ha => ?_⟩
    by_contra hUa
    have h1 := hrel k j hk
    have h2 := hrel a j hUa
    exact hd' a k ha (mul_left_cancel₀ hc (h2.symm.trans h1))
  obtain ⟨p, hp⟩ := la_exists_perm_of_columns U hU hcol
  refine ⟨p, fun i j hij => ?_, fun j => hrel (p j) j (hp j).1⟩
  by_contra hne
  exact hij ((hp j).2 i hne)

@[expose] def la_n01 {L : Type} [Field L] : Matrix (Fin 3) (Fin 3) L :=
  !![0, 1, 0; -1, 0, 0; 0, 0, 1]

@[expose] def la_n12 {L : Type} [Field L] : Matrix (Fin 3) (Fin 3) L :=
  !![1, 0, 0; 0, 0, 1; 0, -1, 0]

private theorem la_cols_of_conj {L : Type} [Field L] (X : Matrix (Fin 3) (Fin 3) L)
    (hdet : X.det ≠ 0)
    (hconj : ∀ i j : Fin 3, i ≠ j → ∃ (k l : Fin 3) (c : L), k ≠ l ∧ ∀ t : L,
      X * (1 + t • Matrix.single i j (1 : L)) = (1 + (c * t) • Matrix.single k l (1 : L)) * X) :
    ∀ i, ∃ k, X k i ≠ 0 ∧ ∀ a, a ≠ k → X a i = 0 := by
  intro i
  have hij : i ≠ i + 1 := by revert i; decide
  obtain ⟨k, l, c, hkl, ht⟩ := hconj i (i + 1) hij
  have h1 := ht 1
  have hrow : ∀ a, X a i = c * (Matrix.single k l (1 : L) * X) a (i + 1) := by
    intro a
    have := congrFun (congrFun h1 a) (i + 1)
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, one_smul,
      mul_one, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_single_apply_same] at this
    exact add_left_cancel this
  have hzero : ∀ a, a ≠ k → X a i = 0 := by
    intro a ha
    rw [hrow a, Matrix.single_mul_apply_of_ne _ _ _ _ _ ha, mul_zero]
  refine ⟨k, ?_, hzero⟩
  intro h0
  apply hdet
  refine Matrix.det_eq_zero_of_column_eq_zero i fun a => ?_
  by_cases ha : a = k
  · rw [ha, h0]
  · exact hzero a ha

private theorem la_mul_monomial_apply {L : Type} [Field L] (X A : Matrix (Fin 3) (Fin 3) L)
    (p : Equiv.Perm (Fin 3)) (hz : ∀ j a, a ≠ p j → X a j = 0) (a j : Fin 3) :
    (A * X) a j = A a (p j) * X (p j) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (p j)]
  · intro b _ hb
    rw [hz j b hb, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem la_cube_apply {L : Type} [Field L] (X : Matrix (Fin 3) (Fin 3) L)
    (p : Equiv.Perm (Fin 3)) (hz : ∀ j a, a ≠ p j → X a j = 0) (a j : Fin 3) :
    (X * X * X) a j = X a (p (p j)) * X (p (p j)) (p j) * X (p j) j := by
  rw [la_mul_monomial_apply X (X * X) p hz, la_mul_monomial_apply X X p hz]

private theorem la_perm_cube {L : Type} [Field L] (X : Matrix (Fin 3) (Fin 3) L)
    (p : Equiv.Perm (Fin 3)) (hp : ∀ j, X (p j) j ≠ 0 ∧ ∀ a, a ≠ p j → X a j = 0) (ξ : L)
    (hξ : X * X * X = ξ • (1 : Matrix (Fin 3) (Fin 3) L)) (j : Fin 3) : p (p (p j)) = j := by
  have hz : ∀ j a, a ≠ p j → X a j = 0 := fun j a ha => (hp j).2 a ha
  have h := la_cube_apply X p hz (p (p (p j))) j
  rw [hξ] at h
  by_contra hne
  have h0 : (ξ • (1 : Matrix (Fin 3) (Fin 3) L)) (p (p (p j))) j = 0 := by
    simp [hne]
  rw [h0] at h
  exact mul_ne_zero (mul_ne_zero (hp (p (p j))).1 (hp (p j)).1) (hp j).1 h.symm

private theorem la_krylov_det_ne_zero {L : Type} [Field L] (X : Matrix (Fin 3) (Fin 3) L)
    (p : Equiv.Perm (Fin 3)) (hp : ∀ j, X (p j) j ≠ 0 ∧ ∀ a, a ≠ p j → X a j = 0)
    (ξ : L) (hξ : X * X * X = ξ • (1 : Matrix (Fin 3) (Fin 3) L))
    (hnd : ¬ ∀ i j : Fin 3, i ≠ j → X i j = 0) :
    (Matrix.of fun a b : Fin 3 => (X ^ (b : ℕ)) a 0).det ≠ 0 := by
  have hz : ∀ j a, a ≠ p j → X a j = 0 := fun j a ha => (hp j).2 a ha
  have hp3 := la_perm_cube X p hp ξ hξ
  have hp1 : ∃ j, p j ≠ j := by
    by_contra hall
    apply hnd
    intro i j hij
    exact hz j i (by rw [not_exists.mp hall j |> not_not.mp]; exact hij)
  have e0 := hp3 0
  have e1 := hp3 1
  rw [Matrix.det_fin_three]
  rcases la_perm_values p with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
    ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · exfalso
    obtain ⟨j, hj⟩ := hp1
    fin_cases j <;> simp [h0, h1, h2] at hj
  · exfalso
    simp [h0, h1] at e0
  · exfalso
    simp [h1, h2] at e1
  · have hx : X 1 0 ≠ 0 := by simpa [h0] using (hp 0).1
    have hy : X 2 1 ≠ 0 := by simpa [h1] using (hp 1).1
    have z00 : X 0 0 = 0 := hz 0 0 (by simp [h0])
    have z20 : X 2 0 = 0 := hz 0 2 (by simp [h0])
    have z01 : X 0 1 = 0 := hz 1 0 (by simp [h1])
    have z11 : X 1 1 = 0 := hz 1 1 (by simp [h1])
    have hXX : ∀ a, (X * X) a 0 = X a 1 * X 1 0 := fun a => by
      rw [la_mul_monomial_apply X X p hz, h0]
    simp [pow_two, hXX, z00, z20, z01, z11, hx, hy]
  · have hx : X 2 0 ≠ 0 := by simpa [h0] using (hp 0).1
    have hy : X 1 2 ≠ 0 := by simpa [h2] using (hp 2).1
    have z00 : X 0 0 = 0 := hz 0 0 (by simp [h0])
    have z10 : X 1 0 = 0 := hz 0 1 (by simp [h0])
    have z02 : X 0 2 = 0 := hz 2 0 (by simp [h2])
    have z22 : X 2 2 = 0 := hz 2 2 (by simp [h2])
    have hXX : ∀ a, (X * X) a 0 = X a 2 * X 2 0 := fun a => by
      rw [la_mul_monomial_apply X X p hz, h0]
    simp [pow_two, hXX, z00, z10, z02, z22, hx, hy]
  · exfalso
    simp [h0, h2] at e0

private theorem la_krylov_comm {L : Type} [Field L] (X : Matrix (Fin 3) (Fin 3) L) (ξ : L)
    (hξ : X * X * X = ξ • (1 : Matrix (Fin 3) (Fin 3) L)) :
    X * (Matrix.of fun a b : Fin 3 => (X ^ (b : ℕ)) a 0) =
      (Matrix.of fun a b : Fin 3 => (X ^ (b : ℕ)) a 0) * !![0, 0, ξ; 1, 0, 0; 0, 1, 0] := by
  have hXK : ∀ a b : Fin 3, (X * (Matrix.of fun a b : Fin 3 => (X ^ (b : ℕ)) a 0)) a b =
      (X ^ ((b : ℕ) + 1)) a 0 := by
    intro a b
    rw [Matrix.mul_apply, pow_succ', Matrix.mul_apply]
    rfl
  ext a b
  rw [hXK, Matrix.mul_apply]
  simp only [Fin.sum_univ_three]
  fin_cases b
  · simp
  · simp [pow_two]
  · have h3 : (X ^ 3) a 0 = ξ * (1 : Matrix (Fin 3) (Fin 3) L) a 0 := by
      rw [pow_succ, pow_two, hξ]
      simp
    simp [h3, mul_comm]

private theorem la_companion_vander {L : Type} [Field L] (ξ : L) (μ : Fin 3 → L)
    (hμ0 : ∀ j, μ j ≠ 0) (hμ3 : ∀ j, μ j ^ 3 = ξ) :
    (!![0, 0, ξ; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) L) *
        (Matrix.vandermonde fun j => (μ j)⁻¹)ᵀ =
      (Matrix.vandermonde fun j => (μ j)⁻¹)ᵀ * Matrix.diagonal μ := by
  ext a j
  have hj := hμ0 j
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simp only [Fin.sum_univ_three, Matrix.transpose_apply, Matrix.vandermonde_apply]
  fin_cases a
  · simp
    rw [← hμ3 j]
    field_simp
  · simp
    field_simp
  · simp
    field_simp

private theorem la_eigenbasis_of_krylov {L : Type} [Field L] (X : Matrix (Fin 3) (Fin 3) L)
    (ξ : L) (hξ : X * X * X = ξ • (1 : Matrix (Fin 3) (Fin 3) L))
    (hK : (Matrix.of fun a b : Fin 3 => (X ^ (b : ℕ)) a 0).det ≠ 0)
    (μ : Fin 3 → L) (hμ0 : ∀ j, μ j ≠ 0) (hμ3 : ∀ j, μ j ^ 3 = ξ)
    (hμinj : Function.Injective μ) :
    ∃ y : Matrix (Fin 3) (Fin 3) L, y.det ≠ 0 ∧ X * y = y * Matrix.diagonal μ := by
  refine ⟨(Matrix.of fun a b : Fin 3 => (X ^ (b : ℕ)) a 0) *
    (Matrix.vandermonde fun j => (μ j)⁻¹)ᵀ, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_transpose]
    refine mul_ne_zero hK ?_
    rw [Matrix.det_vandermonde_ne_zero_iff]
    intro i j hij
    exact hμinj (inv_injective hij)
  · rw [← Matrix.mul_assoc, la_krylov_comm X ξ hξ, Matrix.mul_assoc,
      la_companion_vander ξ μ hμ0 hμ3, ← Matrix.mul_assoc]

private theorem la_det_of_krylov {L : Type} [Field L] (X : Matrix (Fin 3) (Fin 3) L) (ξ : L)
    (hξ : X * X * X = ξ • (1 : Matrix (Fin 3) (Fin 3) L))
    (hK : (Matrix.of fun a b : Fin 3 => (X ^ (b : ℕ)) a 0).det ≠ 0) : X.det = ξ := by
  have h := congrArg Matrix.det (la_krylov_comm X ξ hξ)
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm] at h
  have h2 := mul_left_cancel₀ hK h
  rw [h2, Matrix.det_fin_three]
  simp

private theorem la_cube_roots {L : Type} [Field L] {ω : L} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (lam : L) (hlam0 : lam ≠ 0) (ξ : L) (hlam : lam ^ 3 = ξ) :
    (∀ j, (![lam, ω * lam, ω ^ 2 * lam] : Fin 3 → L) j ≠ 0) ∧
      (∀ j, (![lam, ω * lam, ω ^ 2 * lam] : Fin 3 → L) j ^ 3 = ξ) ∧
      Function.Injective (![lam, ω * lam, ω ^ 2 * lam] : Fin 3 → L) := by
  have hω0 : ω ≠ 0 := by
    intro h
    rw [h] at hω3
    norm_num at hω3
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h
    apply hω1
    calc ω = ω * ω ^ 2 := by rw [h, mul_one]
      _ = ω ^ 3 := by ring
      _ = 1 := hω3
  have hωω : ω ≠ ω ^ 2 := by
    intro h
    have h' : ω * (ω - 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact hω0 h1
    · exact hω1 (sub_eq_zero.mp h1)
  have h01 : lam ≠ ω * lam := fun h => hω1 (mul_right_cancel₀ hlam0 (by linear_combination -h))
  have h02 : lam ≠ ω ^ 2 * lam := fun h =>
    hω2 (mul_right_cancel₀ hlam0 (by linear_combination -h))
  refine ⟨?_, ?_, ?_⟩
  · intro j
    fin_cases j <;> simp [hlam0, hω0]
  · intro j
    fin_cases j
    · simpa using hlam
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      linear_combination lam ^ 3 * hω3 + hlam
    · simp only [Fin.reduceFinMk, Matrix.cons_val]
      linear_combination (lam ^ 3 * (ω ^ 3 + 1)) * hω3 + hlam
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    all_goals first
      | exact h01 hij | exact h01 hij.symm | exact h02 hij | exact h02 hij.symm
      | (rcases hij with h | h <;> first | exact hωω h | exact hωω h.symm | exact hlam0 h)

theorem la_diag_of_monomial_cycle {L : Type} [Field L] {ω : L} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (X : Matrix (Fin 3) (Fin 3) L) (hdet : X.det ≠ 0)
    (hconj : ∀ i j : Fin 3, i ≠ j → ∃ (k l : Fin 3) (c : L), k ≠ l ∧ ∀ t : L,
      X * (1 + t • Matrix.single i j (1 : L)) = (1 + (c * t) • Matrix.single k l (1 : L)) * X)
    (hcube : ∃ ξ : L, X * X * X = ξ • (1 : Matrix (Fin 3) (Fin 3) L))
    (hnd : ¬ ∀ i j : Fin 3, i ≠ j → X i j = 0)
    (lam : L) (hlam : lam ^ 3 = X.det) :
    ∃ y : Matrix (Fin 3) (Fin 3) L, y.det = 1 ∧
      X * y = y * Matrix.diagonal ![lam, ω * lam, ω ^ 2 * lam] := by
  obtain ⟨ξ, hξ⟩ := hcube
  obtain ⟨p, hp⟩ := la_exists_perm_of_columns X hdet (la_cols_of_conj X hdet hconj)
  have hK := la_krylov_det_ne_zero X p hp ξ hξ hnd
  have hdetξ : X.det = ξ := la_det_of_krylov X ξ hξ hK
  have hlam0 : lam ≠ 0 := by
    intro h
    apply hdet
    rw [← hlam, h]
    norm_num
  obtain ⟨hμ0, hμ3, hμinj⟩ := la_cube_roots hω3 hω1 lam hlam0 ξ (hlam.trans hdetξ)
  obtain ⟨y0, hy0, hXy0⟩ :=
    la_eigenbasis_of_krylov X ξ hξ hK ![lam, ω * lam, ω ^ 2 * lam] hμ0 hμ3 hμinj
  refine ⟨y0 * Matrix.diagonal ![(y0.det)⁻¹, 1, 1], ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_three]
    simp [hy0]
  · rw [← Matrix.mul_assoc, hXy0, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 2
    ext j
    simp [mul_comm]

end CFSG.GH74.GLS.Stage2.Bender.Thm1
