module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QOBlk

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Matrix
open CFSG.ComponentClassification.Burgoyne.O (wRes)
open CFSG.ComponentClassification.Burgoyne.PSL (blockOn blockOn_apply_mem blockOn_apply_not_mem
  blockOn_mul det_blockOn)

variable {K : Type} [Field K] {d : ℕ}

variable (K) in
@[expose] def blkScal (J : Finset (Fin d)) (Y : Matrix (Fin J.card) (Fin J.card) K) (c : K) :
    Matrix (Fin d) (Fin d) K :=
  blockOn K J Y * diagonal fun i => if i ∈ J then 1 else c

theorem blkScal_apply_mem {J : Finset (Fin d)} (Y : Matrix (Fin J.card) (Fin J.card) K) (c : K)
    {x y : Fin d} (hx : x ∈ J) (hy : y ∈ J) :
    blkScal K J Y c x y = Y (J.equivFin ⟨x, hx⟩) (J.equivFin ⟨y, hy⟩) := by
  rw [blkScal, mul_diagonal, ite_eq_left hy, mul_one, blockOn_apply_mem _ _ hx hy]

theorem blkScal_apply_not_mem {J : Finset (Fin d)} (Y : Matrix (Fin J.card) (Fin J.card) K)
    (c : K) {x y : Fin d} (h : x ∉ J ∨ y ∉ J) :
    blkScal K J Y c x y = if x = y then c else 0 := by
  rw [blkScal, mul_diagonal, blockOn_apply_not_mem _ _ h]
  by_cases hxy : x = y
  · subst hxy
    have hx : x ∉ J := h.elim id id
    rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_right hx, one_mul]
  · rw [ite_eq_right hxy, ite_eq_right hxy, zero_mul]

theorem blockOn_mul_diagonal_comm (J : Finset (Fin d)) (Y : Matrix (Fin J.card) (Fin J.card) K)
    (c : K) :
    (diagonal fun i => if i ∈ J then (1 : K) else c) * blockOn K J Y =
      blockOn K J Y * diagonal fun i => if i ∈ J then 1 else c := by
  ext x y
  rw [diagonal_mul, mul_diagonal]
  by_cases hx : x ∈ J <;> by_cases hy : y ∈ J
  · rw [ite_eq_left hx, ite_eq_left hy, one_mul, mul_one]
  · rw [blockOn_apply_not_mem _ _ (Or.inr hy), ite_eq_right (fun h : x = y => hy (h ▸ hx)),
      mul_zero, zero_mul]
  · rw [blockOn_apply_not_mem _ _ (Or.inl hx), ite_eq_right (fun h : x = y => hx (h ▸ hy)),
      mul_zero, zero_mul]
  · rw [ite_eq_right hx, ite_eq_right hy, mul_comm]

theorem blkScal_mul (J : Finset (Fin d)) (Y Y' : Matrix (Fin J.card) (Fin J.card) K) (c c' : K) :
    blkScal K J Y c * blkScal K J Y' c' = blkScal K J (Y * Y') (c * c') := by
  rw [blkScal, blkScal, blkScal, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _),
    blockOn_mul_diagonal_comm, Matrix.mul_assoc, diagonal_mul_diagonal, ← Matrix.mul_assoc,
    ← blockOn_mul]
  congr 2
  funext i
  by_cases hi : i ∈ J
  · rw [ite_eq_left hi, ite_eq_left hi, ite_eq_left hi, one_mul]
  · rw [ite_eq_right hi, ite_eq_right hi, ite_eq_right hi]

theorem det_blkScal (J : Finset (Fin d)) (Y : Matrix (Fin J.card) (Fin J.card) K) (c : K) :
    (blkScal K J Y c).det = Y.det * c ^ Jᶜ.card := by
  rw [blkScal, det_mul, det_blockOn, det_diagonal, Finset.prod_ite, Finset.prod_const_one,
    one_mul, Finset.prod_const]
  congr 2
  exact congrArg Finset.card (by ext i; simp)

theorem blkScal_inj {J : Finset (Fin d)} (hJc : Jᶜ.Nonempty)
    {Y Y' : Matrix (Fin J.card) (Fin J.card) K} {c c' : K}
    (h : blkScal K J Y c = blkScal K J Y' c') : Y = Y' ∧ c = c' := by
  refine ⟨?_, ?_⟩
  · ext a b
    have e := congrFun (congrFun h (J.equivFin.symm a)) (J.equivFin.symm b)
    rw [blkScal_apply_mem _ _ (J.equivFin.symm a).2 (J.equivFin.symm b).2,
      blkScal_apply_mem _ _ (J.equivFin.symm a).2 (J.equivFin.symm b).2] at e
    simpa only [Subtype.coe_eta, Equiv.apply_symm_apply] using e
  · obtain ⟨x, hx⟩ := hJc
    have hx' : x ∉ J := Finset.mem_compl.1 hx
    have e := congrFun (congrFun h x) x
    rwa [blkScal_apply_not_mem _ _ (Or.inl hx'), blkScal_apply_not_mem _ _ (Or.inl hx'),
      ite_eq_left rfl, ite_eq_left rfl] at e

theorem eq_blkScal {J : Finset (Fin d)} {D : Matrix (Fin d) (Fin d) K} {c : K}
    (hiso : ∀ x ∈ J, ∀ y ∉ J, D x y = 0 ∧ D y x = 0)
    (hsc : ∀ x ∉ J, ∀ y ∉ J, D x y = if x = y then c else 0) :
    D = blkScal K J (Matrix.of fun a b => D (J.equivFin.symm a) (J.equivFin.symm b)) c := by
  ext x y
  by_cases hx : x ∈ J <;> by_cases hy : y ∈ J
  · rw [blkScal_apply_mem _ _ hx hy, of_apply]
    simp
  · rw [blkScal_apply_not_mem _ _ (Or.inr hy), ite_eq_right (fun h : x = y => hy (h ▸ hx))]
    exact (hiso x hx y hy).1
  · rw [blkScal_apply_not_mem _ _ (Or.inl hx), ite_eq_right (fun h : x = y => hx (h ▸ hy))]
    exact (hiso y hy x hx).2
  · rw [blkScal_apply_not_mem _ _ (Or.inl hx)]
    exact hsc x hx y hy

theorem blkScal_isometry {J : Finset (Fin d)} (hJc : Jᶜ.Nonempty) {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {Y : Matrix (Fin J.card) (Fin J.card) K} {c : K}
    (h : (blkScal K J Y c)ᵀ * diagonal w * blkScal K J Y c = diagonal w) :
    Yᵀ * diagonal (wRes w J) * Y = diagonal (wRes w J) ∧ c ^ 2 = 1 := by
  have key : ∀ x y, ∑ k, blkScal K J Y c k x * w k * blkScal K J Y c k y =
      if x = y then w x else 0 := by
    intro x y
    have e := congrFun (congrFun h x) y
    rw [mul_apply] at e
    simp only [mul_diagonal, transpose_apply, diagonal_apply] at e
    exact e
  refine ⟨?_, ?_⟩
  · ext a b
    have e := key (J.equivFin.symm a) (J.equivFin.symm b)
    rw [sum_eq_sum_equivFin _ fun z hz => by
      rw [blkScal_apply_not_mem _ _ (Or.inl hz),
        ite_eq_right (fun h : z = J.equivFin.symm a => hz (h ▸ (J.equivFin.symm a).2)),
        zero_mul, zero_mul]] at e
    have hiff : ((J.equivFin.symm a : Fin d) = J.equivFin.symm b) ↔ a = b := by
      rw [Subtype.coe_inj, Equiv.apply_eq_iff_eq]
    simp only [blkScal_apply_mem _ _ (J.equivFin.symm _).2 (J.equivFin.symm _).2,
      Subtype.coe_eta, Equiv.apply_symm_apply, hiff] at e
    rw [mul_apply]
    simp only [mul_diagonal, transpose_apply, diagonal_apply]
    exact e
  · obtain ⟨x, hx⟩ := hJc
    have hx' : x ∉ J := Finset.mem_compl.1 hx
    have e := key x x
    rw [Finset.sum_eq_single x (fun k _ hk => by
      rw [blkScal_apply_not_mem _ _ (Or.inr hx'), ite_eq_right hk, zero_mul, zero_mul])
      (fun h => absurd (Finset.mem_univ x) h), blkScal_apply_not_mem _ _ (Or.inl hx'),
      ite_eq_left rfl, ite_eq_left rfl] at e
    have h' : (c ^ 2 - 1) * w x = 0 := by linear_combination e
    exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_right (hw x))

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
