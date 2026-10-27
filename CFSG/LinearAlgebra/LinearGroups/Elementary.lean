module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

public section

namespace CFSG.LinearGroups

open Matrix
open scoped commutatorElement

variable {K : Type*} [Field K] {n : ℕ}

theorem elementary_matrix_identities {i j : Fin n} (hij : i ≠ j) :
    (∀ t : K, (1 + single i j t : Matrix (Fin n) (Fin n) K).det = 1) ∧
      (∀ s t : K, (1 + single i j s : Matrix (Fin n) (Fin n) K) * (1 + single i j t) =
        1 + single i j (s + t)) ∧
      (∀ t : K, (1 + single i j t : Matrix (Fin n) (Fin n) K)⁻¹ = 1 + single i j (-t)) ∧
      (1 + single i j (0 : K) : Matrix (Fin n) (Fin n) K) = 1 := by
  have hmul : ∀ s t : K, (1 + single i j s : Matrix (Fin n) (Fin n) K) * (1 + single i j t) =
      1 + single i j (s + t) := fun s t => transvection_mul_transvection_same i j hij s t
  refine ⟨fun t => det_transvection_of_ne i j hij t, hmul, fun t => ?_, by simp⟩
  apply Matrix.inv_eq_right_inv
  rw [hmul, add_neg_cancel, single_zero, add_zero]

theorem coe_transvection {i j : Fin n} (hij : i ≠ j) (c : K) :
    ((SpecialLinearGroup.transvection hij c : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 + single i j c := rfl

theorem elementary_three_index_commutator {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (s t : K) :
    (1 + single i k s : Matrix (Fin n) (Fin n) K) * (1 + single k j t) *
        (1 + single i k s)⁻¹ * (1 + single k j t)⁻¹ = 1 + single i j (s * t) := by
  have h := congrArg (fun A : SpecialLinearGroup (Fin n) K => (A : Matrix (Fin n) (Fin n) K))
    (SpecialLinearGroup.commutatorElement_transvection hik hjk.symm hij s t)
  simp only [commutatorElement_def, SpecialLinearGroup.transvection_inv, coe_transvection] at h
  rw [(elementary_matrix_identities hik).2.2.1, (elementary_matrix_identities hjk.symm).2.2.1]
  exact h

@[expose] def weylElement (i j : Fin n) (t : K) : Matrix (Fin n) (Fin n) K :=
  (1 + single i j t) * (1 + single j i (-t⁻¹)) * (1 + single i j t)

theorem weylElement_eq {i j : Fin n} (hij : i ≠ j) {t : K} (ht : t ≠ 0) :
    weylElement i j t = 1 + single i j t + single j i (-t⁻¹) - single i i 1 - single j j 1 := by
  ext a b
  simp only [weylElement, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.single_apply]
  by_cases hai : a = i <;> by_cases haj : a = j <;> by_cases hbi : b = i <;>
    by_cases hbj : b = j <;>
    simp_all [Finset.sum_add_distrib, add_mul, mul_add, Finset.sum_ite_eq, eq_comm, ite_and]

@[expose] def elementarySet (n : ℕ) (K : Type*) [Field K] : Set (SpecialLinearGroup (Fin n) K) :=
  {A | ∃ (i j : Fin n) (hij : i ≠ j) (c : K), A = SpecialLinearGroup.transvection hij c}

theorem transvection_mem_elementarySet {i j : Fin n} (hij : i ≠ j) (c : K) :
    SpecialLinearGroup.transvection hij c ∈ elementarySet n K := ⟨i, j, hij, c, rfl⟩

theorem weylElement_mulVec_single {i j : Fin n} (hij : i ≠ j) {t : K} (ht : t ≠ 0) (k : Fin n) :
    weylElement i j t *ᵥ Pi.single k 1 =
      if k = i then (-t⁻¹) • Pi.single j 1 else if k = j then t • Pi.single i 1
        else Pi.single k 1 := by
  rw [weylElement_eq hij ht]
  funext l
  simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.single_apply, Pi.single_apply]
  by_cases hki : k = i <;> by_cases hkj : k = j <;> by_cases hli : l = i <;>
    by_cases hlj : l = j <;>
    simp_all [Finset.sum_ite_eq, eq_comm, ite_and, Pi.single_apply]

theorem elementary_diagonal_factorization {i j : Fin n} (hij : i ≠ j) {t : K} (ht : t ≠ 0) :
    weylElement i j t *ᵥ Pi.single i 1 = (-t⁻¹) • Pi.single j 1 ∧
      weylElement i j t *ᵥ Pi.single j 1 = t • Pi.single i 1 ∧
      (∀ k, k ≠ i → k ≠ j → weylElement i j t *ᵥ Pi.single k 1 = Pi.single k 1) ∧
      diagonal (fun k => if k = i then t else if k = j then t⁻¹ else 1) =
        weylElement i j t * weylElement i j (-1) ∧
      SpecialLinearGroup.diag2n hij t ht ∈ Subgroup.closure (elementarySet n K) := by
  have hW := weylElement_mulVec_single (K := K) hij ht
  have hW1 := weylElement_mulVec_single (K := K) hij (neg_ne_zero.mpr one_ne_zero)
  have hdiag : diagonal (fun k => if k = i then t else if k = j then t⁻¹ else 1) =
      weylElement i j t * weylElement i j (-1) := by
    apply Matrix.ext_of_mulVec_single
    intro k
    rw [← Matrix.mulVec_mulVec, hW1 k, Matrix.mulVec_single_one]
    by_cases hki : k = i
    · subst hki
      rw [ite_eq_left rfl, Matrix.mulVec_smul, hW j, ite_eq_right (Ne.symm hij), ite_eq_left rfl]
      funext l
      simp [Pi.single_apply, Matrix.diagonal_apply]
      split_ifs <;> simp_all
    · by_cases hkj : k = j
      · subst hkj
        rw [ite_eq_right hki, ite_eq_left rfl, Matrix.mulVec_smul, hW i, ite_eq_left rfl]
        funext l
        simp [Pi.single_apply, Matrix.diagonal_apply]
        split_ifs <;> simp_all
      · rw [ite_eq_right hki, ite_eq_right hkj, hW k, ite_eq_right hki, ite_eq_right hkj]
        funext l
        simp [Pi.single_apply, Matrix.diagonal_apply]
        split_ifs <;> simp_all
  refine ⟨by simpa using hW i, by simpa [Ne.symm hij] using hW j,
    fun k hki hkj => by simpa [hki, hkj] using hW k, hdiag, ?_⟩
  have hprod : SpecialLinearGroup.diag2n hij t ht =
      SpecialLinearGroup.transvection hij t * SpecialLinearGroup.transvection hij.symm (-t⁻¹) *
        SpecialLinearGroup.transvection hij t * (SpecialLinearGroup.transvection hij (-1) *
          SpecialLinearGroup.transvection hij.symm (-(-1)⁻¹) *
            SpecialLinearGroup.transvection hij (-1)) := by
    apply Subtype.ext
    rw [SpecialLinearGroup.diag2n_coe, hdiag]
    rfl
  rw [hprod]
  have hT := fun {a b : Fin n} (hab : a ≠ b) (c : K) =>
    Subgroup.subset_closure (transvection_mem_elementarySet (K := K) hab c)
  exact mul_mem (mul_mem (mul_mem (hT _ _) (hT _ _)) (hT _ _))
    (mul_mem (mul_mem (hT _ _) (hT _ _)) (hT _ _))

@[expose] def transvectionDiagConj (d : Fin n → K) (t : TransvectionStruct (Fin n) K) :
    TransvectionStruct (Fin n) K :=
  ⟨t.i, t.j, t.hij, d t.i * t.c * (d t.j)⁻¹⟩

theorem diagonal_mul_toMatrix_mul_diagonal_inv {d : Fin n → K} (hd : ∀ k, d k ≠ 0)
    (t : TransvectionStruct (Fin n) K) :
    diagonal d * t.toMatrix * diagonal (fun k => (d k)⁻¹) =
      (transvectionDiagConj d t).toMatrix := by
  obtain ⟨i, j, hij, c⟩ := t
  ext a b
  simp only [transvectionDiagConj, TransvectionStruct.toMatrix_mk, transvection,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    have := hd a
    by_cases hia : i = a <;> by_cases hja : j = a <;> simp_all
  · by_cases hia : i = a <;> by_cases hjb : j = b <;> simp_all

theorem diagonal_mul_prod_mul_diagonal_inv {d : Fin n → K} (hd : ∀ k, d k ≠ 0)
    (L : List (TransvectionStruct (Fin n) K)) :
    diagonal d * (L.map TransvectionStruct.toMatrix).prod * diagonal (fun k => (d k)⁻¹) =
      ((L.map (transvectionDiagConj d)).map TransvectionStruct.toMatrix).prod := by
  have hinv : diagonal (fun k => (d k)⁻¹) * diagonal d = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    exact inv_mul_cancel₀ (hd k)
  induction L with
  | nil =>
    simp only [List.map_nil, List.prod_nil, Matrix.mul_one, diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    funext k
    exact mul_inv_cancel₀ (hd k)
  | cons t L ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.map_cons, List.prod_cons, ← ih,
      ← diagonal_mul_toMatrix_mul_diagonal_inv hd t]
    calc diagonal d * (t.toMatrix * (L.map TransvectionStruct.toMatrix).prod) *
          diagonal (fun k => (d k)⁻¹) =
        diagonal d * t.toMatrix * (diagonal (fun k => (d k)⁻¹) * diagonal d) *
          (L.map TransvectionStruct.toMatrix).prod * diagonal (fun k => (d k)⁻¹) := by
          rw [hinv, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem row_addition_diagonalization (A : GL (Fin n) K) :
    ∃ (L : List (TransvectionStruct (Fin n) K)) (d : Fin n → K), (∀ i, d i ≠ 0) ∧
      (L.map TransvectionStruct.toMatrix).prod * (A : Matrix (Fin n) (Fin n) K) = diagonal d := by
  obtain ⟨L, L', d, h⟩ :=
    Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal (A : Matrix (Fin n) (Fin n) K)
  have hdet : (diagonal d).det ≠ 0 := by
    rw [← h, det_mul, det_mul, TransvectionStruct.det_toMatrix_prod,
      TransvectionStruct.det_toMatrix_prod, one_mul, mul_one]
    exact (Matrix.isUnit_iff_isUnit_det _).mp A.isUnit |>.ne_zero
  have hd : ∀ i, d i ≠ 0 := by
    rw [det_diagonal] at hdet
    exact fun i => (Finset.prod_ne_zero_iff.mp hdet) i (Finset.mem_univ i)
  refine ⟨L'.map (transvectionDiagConj d) ++ L, d, hd, ?_⟩
  have hL' := TransvectionStruct.prod_mul_reverse_inv_prod L'
  rw [List.map_append, List.prod_append, ← diagonal_mul_prod_mul_diagonal_inv hd L']
  have hLA : (L.map TransvectionStruct.toMatrix).prod * (A : Matrix (Fin n) (Fin n) K) =
      diagonal d *
        (L'.reverse.map (TransvectionStruct.toMatrix ∘ TransvectionStruct.inv)).prod := by
    rw [← h, Matrix.mul_assoc _ (L'.map TransvectionStruct.toMatrix).prod, hL', Matrix.mul_one]
  have hinv : diagonal (fun k => (d k)⁻¹) * diagonal d = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    exact inv_mul_cancel₀ (hd k)
  rw [Matrix.mul_assoc, hLA, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _) (diagonal d),
    hinv, Matrix.one_mul, Matrix.mul_assoc, hL', Matrix.mul_one]

end CFSG.LinearGroups
