module

public import CFSG.LargeExtraspecial.DWModelMat
public import CFSG.LargeExtraspecial.D73GL
public import Mathlib.GroupTheory.Nilpotent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW.D73

open Subgroup Matrix
open scoped MatrixGroups

variable {N : ℕ}

@[expose] def idx0 (hN : 2 ≤ N) : Fin N := ⟨0, by omega⟩

@[expose] def idxL (hN : 2 ≤ N) : Fin N := ⟨N - 1, by omega⟩

@[expose] def midIdx {N : ℕ} (i : Fin (N - 2)) : Fin N := ⟨i.val + 1, by omega⟩

@[simp] theorem val_idx0 (hN : 2 ≤ N) : (idx0 hN).val = 0 := rfl

@[simp] theorem val_idxL (hN : 2 ≤ N) : (idxL hN).val = N - 1 := rfl

@[simp] theorem val_midIdx (i : Fin (N - 2)) : (midIdx i : Fin N).val = i.val + 1 := rfl

theorem midIdx_injective : Function.Injective (midIdx : Fin (N - 2) → Fin N) := fun i j h =>
  Fin.ext (by simpa [Fin.ext_iff] using h)

@[simp] theorem midIdx_inj {i j : Fin (N - 2)} : (midIdx i : Fin N) = midIdx j ↔ i = j :=
  midIdx_injective.eq_iff

variable (hN : 2 ≤ N)

@[simp] theorem midIdx_ne_idx0 (i : Fin (N - 2)) : midIdx i ≠ idx0 hN := fun h => by
  simp [Fin.ext_iff] at h

@[simp] theorem midIdx_ne_idxL (i : Fin (N - 2)) : midIdx i ≠ idxL hN := fun h => by
  have := i.isLt
  simp [Fin.ext_iff] at h
  omega

@[simp] theorem idx0_ne_midIdx (i : Fin (N - 2)) : idx0 hN ≠ midIdx i :=
  (midIdx_ne_idx0 hN i).symm

@[simp] theorem idxL_ne_midIdx (i : Fin (N - 2)) : idxL hN ≠ midIdx i :=
  (midIdx_ne_idxL hN i).symm

@[simp] theorem idx0_ne_idxL : idx0 hN ≠ idxL hN := fun h => by
  simp [Fin.ext_iff] at h
  omega

@[simp] theorem idxL_ne_idx0 : idxL hN ≠ idx0 hN := (idx0_ne_idxL hN).symm

@[expose] def idxEquiv : Fin (N - 2) ⊕ Fin 2 ≃ Fin N where
  toFun := Sum.elim midIdx ![idx0 hN, idxL hN]
  invFun k := if h0 : k.val = 0 then Sum.inr 0 else if hL : k.val = N - 1 then Sum.inr 1
    else Sum.inl ⟨k.val - 1, by omega⟩
  left_inv := by
    rintro (i | t)
    · have h1 : i.val + 1 ≠ N - 1 := by have := i.isLt; omega
      simp [h1]
    · fin_cases t
      · simp
      · have h1 : N - 1 ≠ 0 := by omega
        simp [h1]
  right_inv k := by
    dsimp only
    by_cases h0 : k.val = 0
    · rw [dite_eq_left h0]
      exact Fin.ext (by simp [h0])
    · by_cases hL : k.val = N - 1
      · rw [dite_eq_right h0, dite_eq_left hL]
        exact Fin.ext (by simp [hL])
      · rw [dite_eq_right h0, dite_eq_right hL]
        exact Fin.ext (by simp; omega)

@[simp] theorem idxEquiv_symm_midIdx (i : Fin (N - 2)) :
    (idxEquiv hN).symm (midIdx i) = Sum.inl i :=
  (Equiv.symm_apply_eq _).mpr rfl

@[simp] theorem idxEquiv_symm_idx0 : (idxEquiv hN).symm (idx0 hN) = Sum.inr 0 :=
  (Equiv.symm_apply_eq _).mpr rfl

@[simp] theorem idxEquiv_symm_idxL : (idxEquiv hN).symm (idxL hN) = Sum.inr 1 :=
  (Equiv.symm_apply_eq _).mpr rfl

theorem idx_cases (k : Fin N) : k = idx0 hN ∨ k = idxL hN ∨ ∃ i, k = midIdx i := by
  rcases h : (idxEquiv hN).symm k with i | t
  · exact Or.inr (Or.inr ⟨i, by rw [← (idxEquiv hN).apply_symm_apply k, h]; rfl⟩)
  · fin_cases t
    · exact Or.inl (by rw [← (idxEquiv hN).apply_symm_apply k, h]; rfl)
    · exact Or.inr (Or.inl (by rw [← (idxEquiv hN).apply_symm_apply k, h]; rfl))

theorem sum_fin_eq {R : Type*} [AddCommMonoid R] (f : Fin N → R) :
    ∑ k, f k = f (idx0 hN) + f (idxL hN) + ∑ i : Fin (N - 2), f (midIdx i) := by
  rw [← (idxEquiv hN).sum_comp, Fintype.sum_sum_type, Fin.sum_univ_two, add_comm]
  rfl

abbrev Ct (N : ℕ) (hN : 2 ≤ N) : Subgroup (SL(N, ZMod 2)) :=
  centralizer ({cornerTransvection hN} : Set (SL(N, ZMod 2)))

@[expose] def tZero {N : ℕ} (hN : 2 ≤ N) : Ct N hN :=
  ⟨cornerTransvection hN, mem_centralizer_singleton_iff.mpr rfl⟩

theorem mem_Ct_iff' (g : SL(N, ZMod 2)) :
    g ∈ Ct N hN ↔ (∀ k, (g : Matrix (Fin N) (Fin N) (ZMod 2)) k (idx0 hN) =
        if k = idx0 hN then 1 else 0) ∧
      ∀ l, (g : Matrix (Fin N) (Fin N) (ZMod 2)) (idxL hN) l = if l = idxL hN then 1 else 0 := by
  have ht : ((cornerTransvection hN : SL(N, ZMod 2)) : Matrix (Fin N) (Fin N) (ZMod 2)) =
      Matrix.transvection (idx0 hN) (idxL hN) 1 := rfl
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hm : (g : Matrix (Fin N) (Fin N) (ZMod 2)) * Matrix.transvection (idx0 hN) (idxL hN) 1 =
        Matrix.transvection (idx0 hN) (idxL hN) 1 * (g : Matrix (Fin N) (Fin N) (ZMod 2)) := by
      have := congrArg (fun x : SL(N, ZMod 2) => (x : Matrix (Fin N) (Fin N) (ZMod 2))) h
      simpa only [Matrix.SpecialLinearGroup.coe_mul, ht] using this
    have hcol : ∀ k, k ≠ idx0 hN → (g : Matrix (Fin N) (Fin N) (ZMod 2)) k (idx0 hN) = 0 :=
      fun k hk => by
        have := congrFun (congrFun hm k) (idxL hN)
        rw [mul_transvection_apply_same, transvection_mul_apply_of_ne _ _ _ _ hk] at this
        simpa using this
    have hrow : ∀ l, l ≠ idxL hN → (g : Matrix (Fin N) (Fin N) (ZMod 2)) (idxL hN) l = 0 :=
      fun l hl => by
        have := congrFun (congrFun hm (idx0 hN)) l
        rw [mul_transvection_apply_of_ne _ _ _ _ hl, transvection_mul_apply_same] at this
        simpa using this
    have hdiag : (g : Matrix (Fin N) (Fin N) (ZMod 2)) (idxL hN) (idxL hN) =
        (g : Matrix (Fin N) (Fin N) (ZMod 2)) (idx0 hN) (idx0 hN) := by
      have := congrFun (congrFun hm (idx0 hN)) (idxL hN)
      rw [mul_transvection_apply_same, transvection_mul_apply_same] at this
      simpa using this.symm
    have h00 : (g : Matrix (Fin N) (Fin N) (ZMod 2)) (idx0 hN) (idx0 hN) = 1 := by
      by_contra hne
      have h0 : (g : Matrix (Fin N) (Fin N) (ZMod 2)) (idx0 hN) (idx0 hN) = 0 := by
        revert hne
        generalize (g : Matrix (Fin N) (Fin N) (ZMod 2)) (idx0 hN) (idx0 hN) = d
        revert d
        decide
      have hdet := g.2
      rw [Matrix.det_eq_zero_of_column_eq_zero (idx0 hN) fun k => by
        by_cases hk : k = idx0 hN
        · rw [hk, h0]
        · exact hcol k hk] at hdet
      exact zero_ne_one hdet
    refine ⟨fun k => ?_, fun l => ?_⟩
    · split_ifs with hk
      · rw [hk, h00]
      · exact hcol k hk
    · split_ifs with hl
      · rw [hl, hdiag, h00]
      · exact hrow l hl
  · rintro ⟨hcol, hrow⟩
    refine Matrix.SpecialLinearGroup.ext _ _ fun k l => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ht]
    by_cases hl : l = idxL hN
    · subst hl
      rw [mul_transvection_apply_same]
      by_cases hk : k = idx0 hN
      · subst hk
        rw [transvection_mul_apply_same, hcol, hrow]
        simp
      · rw [transvection_mul_apply_of_ne _ _ _ _ hk, hcol]
        simp [hk]
    · rw [mul_transvection_apply_of_ne _ _ _ _ hl]
      by_cases hk : k = idx0 hN
      · subst hk
        rw [transvection_mul_apply_same, hrow]
        simp [hl]
      · rw [transvection_mul_apply_of_ne _ _ _ _ hk]

variable {hN}

theorem Ct_apply_idx0 (g : Ct N hN) (k : Fin N) :
    ((g : SL(N, ZMod 2)) : Matrix (Fin N) (Fin N) (ZMod 2)) k (idx0 hN) =
      if k = idx0 hN then 1 else 0 :=
  ((mem_Ct_iff' hN g).mp g.2).1 k

theorem Ct_idxL_apply (g : Ct N hN) (l : Fin N) :
    ((g : SL(N, ZMod 2)) : Matrix (Fin N) (Fin N) (ZMod 2)) (idxL hN) l =
      if l = idxL hN then 1 else 0 :=
  ((mem_Ct_iff' hN g).mp g.2).2 l

@[simp] theorem Ct_idx0_idx0 (g : Ct N hN) :
    ((g : SL(N, ZMod 2)) : Matrix (Fin N) (Fin N) (ZMod 2)) (idx0 hN) (idx0 hN) = 1 := by
  simp [Ct_apply_idx0]

@[simp] theorem Ct_midIdx_idx0 (g : Ct N hN) (i : Fin (N - 2)) :
    ((g : SL(N, ZMod 2)) : Matrix (Fin N) (Fin N) (ZMod 2)) (midIdx i) (idx0 hN) = 0 := by
  simp [Ct_apply_idx0]

@[simp] theorem Ct_idxL_idx0 (g : Ct N hN) :
    ((g : SL(N, ZMod 2)) : Matrix (Fin N) (Fin N) (ZMod 2)) (idxL hN) (idx0 hN) = 0 := by
  simp [Ct_apply_idx0]

@[simp] theorem Ct_idxL_idxL (g : Ct N hN) :
    ((g : SL(N, ZMod 2)) : Matrix (Fin N) (Fin N) (ZMod 2)) (idxL hN) (idxL hN) = 1 := by
  simp [Ct_idxL_apply]

@[simp] theorem Ct_idxL_midIdx (g : Ct N hN) (j : Fin (N - 2)) :
    ((g : SL(N, ZMod 2)) : Matrix (Fin N) (Fin N) (ZMod 2)) (idxL hN) (midIdx j) = 0 := by
  simp [Ct_idxL_apply]

variable (hN)

@[expose] noncomputable def midBlockMat :
    Ct N hN →* Matrix (Fin (N - 2)) (Fin (N - 2)) (ZMod 2) where
  toFun g := Matrix.of fun i j =>
    ((g : SL(N, ZMod 2)) : Matrix (Fin N) (Fin N) (ZMod 2)) (midIdx i) (midIdx j)
  map_one' := by
    ext i j
    simp [Matrix.one_apply]
  map_mul' g h := by
    ext i j
    simp only [Matrix.of_apply, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, sum_fin_eq hN, Ct_midIdx_idx0, Ct_idxL_midIdx, zero_mul, mul_zero,
      zero_add]

@[expose] noncomputable def midBlock {N : ℕ} (hN : 2 ≤ N) :
    Ct N hN →* GL (Fin (N - 2)) (ZMod 2) :=
  (midBlockMat hN).toHomUnits

theorem midBlock_apply (g : Ct N hN) (i j : Fin (N - 2)) :
    ((midBlock hN g : GL (Fin (N - 2)) (ZMod 2)) : Matrix (Fin (N - 2)) (Fin (N - 2)) (ZMod 2))
      i j = ((g : SL(N, ZMod 2)) : Matrix (Fin N) (Fin N) (ZMod 2)) (midIdx i) (midIdx j) :=
  rfl

@[expose] def embMat (X : Matrix (Fin (N - 2)) (Fin (N - 2)) (ZMod 2)) :
    Matrix (Fin N) (Fin N) (ZMod 2) :=
  Matrix.reindex (idxEquiv hN) (idxEquiv hN) (Matrix.fromBlocks X 0 0 1)

theorem embMat_apply (X : Matrix (Fin (N - 2)) (Fin (N - 2)) (ZMod 2)) (k l : Fin N) :
    embMat hN X k l = Matrix.fromBlocks X 0 0 1 ((idxEquiv hN).symm k) ((idxEquiv hN).symm l) :=
  rfl

theorem midBlock_surjective : Function.Surjective (midBlock hN) := by
  intro X
  have hdet : (embMat hN (X : Matrix (Fin (N - 2)) (Fin (N - 2)) (ZMod 2))).det = 1 := by
    rw [embMat, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
    refine det_eq_one_of_ne_zero_zmod_two ?_
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  set g : SL(N, ZMod 2) := ⟨embMat hN (X : Matrix (Fin (N - 2)) (Fin (N - 2)) (ZMod 2)), hdet⟩
  have hg : g ∈ Ct N hN := by
    refine (mem_Ct_iff' hN g).mpr ⟨fun k => ?_, fun l => ?_⟩
    · change embMat hN _ k (idx0 hN) = _
      rcases idx_cases hN k with rfl | rfl | ⟨i, rfl⟩ <;> simp [embMat_apply]
    · change embMat hN _ (idxL hN) l = _
      rcases idx_cases hN l with rfl | rfl | ⟨j, rfl⟩ <;> simp [embMat_apply]
  refine ⟨⟨g, hg⟩, Units.ext (Matrix.ext fun i j => ?_)⟩
  rw [midBlock_apply]
  change embMat hN _ (midIdx i) (midIdx j) = _
  simp [embMat_apply]

noncomputable abbrev Qm {N : ℕ} (hN : 2 ≤ N) : Subgroup (Ct N hN) := (midBlock hN).ker

theorem mem_Qm_iff {g : Ct N hN} : g ∈ Qm hN ↔ ∀ i j,
    ((g : SL(N, ZMod 2)) : Matrix (Fin N) (Fin N) (ZMod 2)) (midIdx i) (midIdx j) =
      (1 : Matrix (Fin (N - 2)) (Fin (N - 2)) (ZMod 2)) i j := by
  rw [MonoidHom.mem_ker, Units.ext_iff, Units.val_one, ← Matrix.ext_iff]
  rfl

@[expose] def extVec (a : Fin (N - 2) → ZMod 2) (x y : ZMod 2) : Fin N → ZMod 2 :=
  fun k => Sum.elim a ![x, y] ((idxEquiv hN).symm k)

@[simp] theorem extVec_midIdx (a : Fin (N - 2) → ZMod 2) (x y : ZMod 2) (i : Fin (N - 2)) :
    extVec hN a x y (midIdx i) = a i := by
  simp [extVec]

@[simp] theorem extVec_idx0 (a : Fin (N - 2) → ZMod 2) (x y : ZMod 2) :
    extVec hN a x y (idx0 hN) = x := by
  simp [extVec]

@[simp] theorem extVec_idxL (a : Fin (N - 2) → ZMod 2) (x y : ZMod 2) :
    extVec hN a x y (idxL hN) = y := by
  simp [extVec]

@[expose] def qmatMat (a b : Fin (N - 2) → ZMod 2) (c : ZMod 2) :
    Matrix (Fin N) (Fin N) (ZMod 2) :=
  Matrix.of fun k l => (1 : Matrix (Fin N) (Fin N) (ZMod 2)) k l +
    (if k = idx0 hN then extVec hN a 0 c l else 0) +
      (if l = idxL hN then extVec hN b 0 0 k else 0)

section qmatMat

variable (a b : Fin (N - 2) → ZMod 2) (c : ZMod 2) (i j : Fin (N - 2))

@[simp] theorem qmatMat_idx0_idx0 : qmatMat hN a b c (idx0 hN) (idx0 hN) = 1 := by
  simp [qmatMat]

@[simp] theorem qmatMat_idx0_idxL : qmatMat hN a b c (idx0 hN) (idxL hN) = c := by
  simp [qmatMat]

@[simp] theorem qmatMat_idx0_midIdx : qmatMat hN a b c (idx0 hN) (midIdx j) = a j := by
  simp [qmatMat]

@[simp] theorem qmatMat_idxL_idx0 : qmatMat hN a b c (idxL hN) (idx0 hN) = 0 := by
  simp [qmatMat]

@[simp] theorem qmatMat_idxL_idxL : qmatMat hN a b c (idxL hN) (idxL hN) = 1 := by
  simp [qmatMat]

@[simp] theorem qmatMat_idxL_midIdx : qmatMat hN a b c (idxL hN) (midIdx j) = 0 := by
  simp [qmatMat, Matrix.one_apply]

@[simp] theorem qmatMat_midIdx_idx0 : qmatMat hN a b c (midIdx i) (idx0 hN) = 0 := by
  simp [qmatMat, Matrix.one_apply]

@[simp] theorem qmatMat_midIdx_idxL : qmatMat hN a b c (midIdx i) (idxL hN) = b i := by
  simp [qmatMat, Matrix.one_apply]

@[simp] theorem qmatMat_midIdx_midIdx :
    qmatMat hN a b c (midIdx i) (midIdx j) =
      (1 : Matrix (Fin (N - 2)) (Fin (N - 2)) (ZMod 2)) i j := by
  simp [qmatMat, Matrix.one_apply]

theorem det_qmatMat : (qmatMat hN a b c).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun k _ => ?_
    rcases idx_cases hN k with rfl | rfl | ⟨i, rfl⟩ <;> simp
  · intro k l hlk
    have hlk' : l.val < k.val := hlk
    rcases idx_cases hN k with rfl | rfl | ⟨i, rfl⟩ <;>
      rcases idx_cases hN l with rfl | rfl | ⟨j, rfl⟩ <;> simp at hlk' ⊢
    · have := i.isLt
      omega
    · rw [Matrix.one_apply_ne]
      rintro rfl
      exact lt_irrefl _ hlk'

end qmatMat

@[expose] def qmat (a b : Fin (N - 2) → ZMod 2) (c : ZMod 2) : Ct N hN :=
  ⟨⟨qmatMat hN a b c, det_qmatMat hN a b c⟩, (mem_Ct_iff' hN _).mpr
    ⟨fun k => by rcases idx_cases hN k with rfl | rfl | ⟨i, rfl⟩ <;> simp,
      fun l => by rcases idx_cases hN l with rfl | rfl | ⟨j, rfl⟩ <;> simp⟩⟩

theorem coe_qmat (a b : Fin (N - 2) → ZMod 2) (c : ZMod 2) :
    ((qmat hN a b c : SL(N, ZMod 2)) : Matrix (Fin N) (Fin N) (ZMod 2)) = qmatMat hN a b c :=
  rfl

theorem qmat_mul (a b a' b' : Fin (N - 2) → ZMod 2) (c c' : ZMod 2) :
    qmat hN a b c * qmat hN a' b' c' = qmat hN (a + a') (b + b') (c + c' + a ⬝ᵥ b') := by
  refine Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun k l => ?_)
  simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_qmat, Matrix.mul_apply,
    sum_fin_eq hN]
  rcases idx_cases hN k with rfl | rfl | ⟨i, rfl⟩ <;>
    rcases idx_cases hN l with rfl | rfl | ⟨j, rfl⟩ <;>
    simp [Matrix.one_apply, dotProduct] <;> ring

theorem qmat_mem_Qm (a b : Fin (N - 2) → ZMod 2) (c : ZMod 2) : qmat hN a b c ∈ Qm hN :=
  (mem_Qm_iff hN).mpr fun i j => by simp [coe_qmat]

theorem qmat_injective {a b a' b' : Fin (N - 2) → ZMod 2} {c c' : ZMod 2}
    (h : qmat hN a b c = qmat hN a' b' c') : a = a' ∧ b = b' ∧ c = c' := by
  have hm : qmatMat hN a b c = qmatMat hN a' b' c' :=
    congrArg (fun g : Ct N hN => ((g : SL(N, ZMod 2)) : Matrix (Fin N) (Fin N) (ZMod 2))) h
  refine ⟨funext fun j => ?_, funext fun i => ?_, ?_⟩
  · simpa using congrFun (congrFun hm (idx0 hN)) (midIdx j)
  · simpa using congrFun (congrFun hm (midIdx i)) (idxL hN)
  · simpa using congrFun (congrFun hm (idx0 hN)) (idxL hN)

theorem eq_qmat_of_mem_Qm {g : Ct N hN} (hg : g ∈ Qm hN) :
    g = qmat hN (fun j => ((g : SL(N, ZMod 2)) : Matrix (Fin N) (Fin N) (ZMod 2)) (idx0 hN)
        (midIdx j))
      (fun i => ((g : SL(N, ZMod 2)) : Matrix (Fin N) (Fin N) (ZMod 2)) (midIdx i) (idxL hN))
      (((g : SL(N, ZMod 2)) : Matrix (Fin N) (Fin N) (ZMod 2)) (idx0 hN) (idxL hN)) := by
  have hQ := (mem_Qm_iff hN).mp hg
  refine Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun k l => ?_)
  rw [coe_qmat]
  rcases idx_cases hN k with rfl | rfl | ⟨i, rfl⟩ <;>
    rcases idx_cases hN l with rfl | rfl | ⟨j, rfl⟩ <;> simp [hQ]

theorem qmat_zero : qmat hN 0 0 0 = 1 := by
  refine Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun k l => ?_)
  rw [coe_qmat]
  rcases idx_cases hN k with rfl | rfl | ⟨i, rfl⟩ <;>
    rcases idx_cases hN l with rfl | rfl | ⟨j, rfl⟩ <;> simp [Matrix.one_apply]

theorem tZero_eq_qmat : tZero hN = qmat hN 0 0 1 := by
  refine Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun k l => ?_)
  rw [coe_qmat]
  change Matrix.transvection (idx0 hN) (idxL hN) 1 k l = _
  rcases idx_cases hN k with rfl | rfl | ⟨i, rfl⟩ <;>
    rcases idx_cases hN l with rfl | rfl | ⟨j, rfl⟩ <;>
    simp [Matrix.transvection, Matrix.one_apply]

theorem card_Qm : Nat.card (Qm hN) = 2 ^ (2 * N - 3) := by
  have hbij : Function.Bijective
      (fun x : (Fin (N - 2) → ZMod 2) × (Fin (N - 2) → ZMod 2) × ZMod 2 =>
        (⟨qmat hN x.1 x.2.1 x.2.2, qmat_mem_Qm hN _ _ _⟩ : Qm hN)) := by
    refine ⟨fun x y h => ?_, fun g => ⟨(_, _, _), Subtype.ext (eq_qmat_of_mem_Qm hN g.2).symm⟩⟩
    obtain ⟨h1, h2, h3⟩ := qmat_injective hN (congrArg Subtype.val h)
    exact Prod.ext h1 (Prod.ext h2 h3)
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_prod, Nat.card_prod, Nat.card_fun,
    Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_succ, ← pow_add]
  congr 1
  omega

theorem card_Ct : Nat.card (Ct N hN) = 2 ^ (2 * N - 3) * Nat.card (GL (Fin (N - 2)) (ZMod 2)) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Qm hN), card_Qm,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ (midBlock_surjective hN)).toEquiv,
    mul_comm]

theorem two_pow_dvd_card_Ct : 2 ^ (N * (N - 1) / 2) ∣ Nat.card (Ct N hN) := by
  obtain ⟨u, -, hu⟩ := exists_card_GL_eq (K := ZMod 2) (s := 1) (by simp) (N - 2)
  rw [card_Ct, hu, ← mul_assoc, ← pow_add]
  refine Dvd.dvd.mul_right (pow_dvd_pow 2 (le_of_eq ?_)) u
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  have h1 : (n + 2) * (n + 2 - 1) = n * (n - 1) + 2 * (2 * n + 1) := by
    rcases n with _ | n
    · rfl
    · rw [show n + 1 + 2 - 1 = n + 2 by omega, show n + 1 - 1 = n by omega]
      ring
  rw [h1, Nat.add_mul_div_left _ _ two_pos, show n + 2 - 2 = n by omega,
    show n - 1 = n - 1 from rfl, one_mul]
  omega

end CFSG.LargeExtraspecial.DW.D73
