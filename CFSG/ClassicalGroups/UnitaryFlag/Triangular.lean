module

public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open Matrix CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

@[expose] def blk3 (A : Matrix (Fin r) (Fin r) K) (X : Matrix (Fin r) (Fin ε) K)
    (Y : Matrix (Fin r) (Fin r) K) (P : Matrix (Fin ε) (Fin ε) K) (Q : Matrix (Fin ε) (Fin r) K)
    (D : Matrix (Fin r) (Fin r) K) : Matrix (HypIndex r ε) (HypIndex r ε) K :=
  fromBlocks A (fromCols X Y) 0 (fromBlocks P Q 0 D)

section Blk3

variable (A : Matrix (Fin r) (Fin r) K) (X : Matrix (Fin r) (Fin ε) K)
  (Y : Matrix (Fin r) (Fin r) K) (P : Matrix (Fin ε) (Fin ε) K) (Q : Matrix (Fin ε) (Fin r) K)
  (D : Matrix (Fin r) (Fin r) K)

@[simp] theorem blk3_inl_inl (i j : Fin r) : blk3 A X Y P Q D (.inl i) (.inl j) = A i j := rfl
@[simp] theorem blk3_inl_inr_inl (i : Fin r) (l : Fin ε) :
    blk3 A X Y P Q D (.inl i) (.inr (.inl l)) = X i l := rfl
@[simp] theorem blk3_inl_inr_inr (i j : Fin r) :
    blk3 A X Y P Q D (.inl i) (.inr (.inr j)) = Y i j := rfl
@[simp] theorem blk3_inr_inl_inl (k : Fin ε) (j : Fin r) :
    blk3 A X Y P Q D (.inr (.inl k)) (.inl j) = 0 := rfl
@[simp] theorem blk3_inr_inl_inr_inl (k l : Fin ε) :
    blk3 A X Y P Q D (.inr (.inl k)) (.inr (.inl l)) = P k l := rfl
@[simp] theorem blk3_inr_inl_inr_inr (k : Fin ε) (j : Fin r) :
    blk3 A X Y P Q D (.inr (.inl k)) (.inr (.inr j)) = Q k j := rfl
@[simp] theorem blk3_inr_inr_inl (i j : Fin r) :
    blk3 A X Y P Q D (.inr (.inr i)) (.inl j) = 0 := rfl
@[simp] theorem blk3_inr_inr_inr_inl (i : Fin r) (l : Fin ε) :
    blk3 A X Y P Q D (.inr (.inr i)) (.inr (.inl l)) = 0 := rfl
@[simp] theorem blk3_inr_inr_inr_inr (i j : Fin r) :
    blk3 A X Y P Q D (.inr (.inr i)) (.inr (.inr j)) = D i j := rfl

theorem blk3_mul (A' : Matrix (Fin r) (Fin r) K) (X' : Matrix (Fin r) (Fin ε) K)
    (Y' : Matrix (Fin r) (Fin r) K) (P' : Matrix (Fin ε) (Fin ε) K)
    (Q' : Matrix (Fin ε) (Fin r) K) (D' : Matrix (Fin r) (Fin r) K) :
    blk3 A X Y P Q D * blk3 A' X' Y' P' Q' D' =
      blk3 (A * A') (A * X' + X * P') (A * Y' + X * Q' + Y * D') (P * P') (P * Q' + Q * D')
        (D * D') := by
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j <;>
    simp [mul_apply, Fintype.sum_sum_type, Matrix.add_apply, add_assoc]

theorem det_blk3 : (blk3 A X Y P Q D).det = A.det * P.det * D.det := by
  rw [blk3, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁, mul_assoc]

end Blk3

theorem conjTranspose_hypGram_mul_apply (h : UnitaryFieldData p f K)
    (M : Matrix (HypIndex r ε) (HypIndex r ε) K) (a b : HypIndex r ε) :
    ((M.map h.bar)ᵀ * hypGram r ε K * M) a b = ∑ x, h.bar (M x a) * M (hypPartner x) b := by
  rw [mul_apply]
  simp only [mul_hypGram_apply, transpose_apply, map_apply]
  exact Fintype.sum_equiv (Function.Involutive.toPerm _ hypPartner_involutive) _ _
    fun x => by simp

theorem conjTranspose_mul' {m n o : Type} [Fintype n] (h : UnitaryFieldData p f K)
    (M : Matrix m n K) (N : Matrix n o K) :
    ((M * N).map h.bar)ᵀ = (N.map h.bar)ᵀ * (M.map h.bar)ᵀ := by
  rw [Matrix.map_mul, transpose_mul]

theorem conjTranspose_conjTranspose' {m n : Type} (h : UnitaryFieldData p f K)
    (M : Matrix m n K) : (((M.map h.bar)ᵀ).map h.bar)ᵀ = M := by
  ext i j
  simp [h.bar_bar]

section Gram

variable (h : UnitaryFieldData p f K) (A : Matrix (Fin r) (Fin r) K) (X : Matrix (Fin r) (Fin ε) K)
  (Y : Matrix (Fin r) (Fin r) K) (P : Matrix (Fin ε) (Fin ε) K) (Q : Matrix (Fin ε) (Fin r) K)
  (D : Matrix (Fin r) (Fin r) K)

theorem blk3_gram_iff :
    ((blk3 A X Y P Q D).map h.bar)ᵀ * hypGram r ε K * blk3 A X Y P Q D = hypGram r ε K ↔
      (A.map h.bar)ᵀ * D = 1 ∧ (P.map h.bar)ᵀ * P = 1 ∧
        (X.map h.bar)ᵀ * D + (P.map h.bar)ᵀ * Q = 0 ∧
        (Y.map h.bar)ᵀ * D + (Q.map h.bar)ᵀ * Q + (D.map h.bar)ᵀ * Y = 0 := by
  set G := ((blk3 A X Y P Q D).map h.bar)ᵀ * hypGram r ε K * blk3 A X Y P Q D with hG
  have e11 : ∀ i j, G (.inl i) (.inl j) = 0 := by
    intro i j
    simp [hG, Fintype.sum_sum_type, mul_apply]
  have e12 : ∀ i l, G (.inl i) (.inr (.inl l)) = 0 := by
    intro i l
    simp [hG, Fintype.sum_sum_type, mul_apply]
  have e13 : ∀ i j, G (.inl i) (.inr (.inr j)) = ((A.map h.bar)ᵀ * D) i j := by
    intro i j
    simp [hG, Fintype.sum_sum_type, mul_apply]
  have e21 : ∀ k j, G (.inr (.inl k)) (.inl j) = 0 := by
    intro k j
    simp [hG, Fintype.sum_sum_type, mul_apply]
  have e22 : ∀ k l, G (.inr (.inl k)) (.inr (.inl l)) = ((P.map h.bar)ᵀ * P) k l := by
    intro k l
    simp [hG, Fintype.sum_sum_type, mul_apply]
  have e23 : ∀ k j, G (.inr (.inl k)) (.inr (.inr j)) =
      ((X.map h.bar)ᵀ * D + (P.map h.bar)ᵀ * Q) k j := by
    intro k j
    simp [hG, Fintype.sum_sum_type, mul_apply]
    ring
  have e31 : ∀ i j, G (.inr (.inr i)) (.inl j) = ((D.map h.bar)ᵀ * A) i j := by
    intro i j
    simp [hG, Fintype.sum_sum_type, mul_apply]
  have e32 : ∀ i l, G (.inr (.inr i)) (.inr (.inl l)) =
      ((D.map h.bar)ᵀ * X + (Q.map h.bar)ᵀ * P) i l := by
    intro i l
    simp [hG, Fintype.sum_sum_type, mul_apply]
  have e33 : ∀ i j, G (.inr (.inr i)) (.inr (.inr j)) =
      ((Y.map h.bar)ᵀ * D + (Q.map h.bar)ᵀ * Q + (D.map h.bar)ᵀ * Y) i j := by
    intro i j
    simp [hG, Fintype.sum_sum_type, mul_apply]
    ring
  constructor
  · intro hJ
    have hJ' : ∀ a b, G a b = hypGram r ε K a b := fun a b => by rw [hJ]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ext a b
    · rw [← e13, hJ', hypGram_inl_inr_inr, one_apply]
    · rw [← e22, hJ', hypGram_inr_inl_inr_inl, one_apply]
    · rw [← e23, hJ', hypGram_inr_inl_inr_inr, Matrix.zero_apply]
    · rw [← e33, hJ', hypGram_inr_inr_inr_inr, Matrix.zero_apply]
  · rintro ⟨h1, h2, h3, h4⟩
    have h1' : (D.map h.bar)ᵀ * A = 1 := by
      have := congrArg (fun M => (M.map h.bar)ᵀ) h1
      simp only [conjTranspose_mul', conjTranspose_conjTranspose'] at this
      rw [this, Matrix.map_one _ (map_zero _) (map_one _), transpose_one]
    have h3' : (D.map h.bar)ᵀ * X + (Q.map h.bar)ᵀ * P = 0 := by
      have := congrArg (fun M => (M.map h.bar)ᵀ) h3
      simp only [Matrix.map_add _ (map_add h.bar), transpose_add, conjTranspose_mul',
        conjTranspose_conjTranspose', Matrix.map_zero _ (map_zero h.bar), transpose_zero] at this
      rw [← this, add_comm]
    ext a b
    rcases a with i | k | i <;> rcases b with j | l | j
    · rw [e11, hypGram_inl_inl]
    · rw [e12, hypGram_inl_inr_inl]
    · rw [e13, h1, hypGram_inl_inr_inr, one_apply]
    · rw [e21, hypGram_inr_inl_inl]
    · rw [e22, h2, hypGram_inr_inl_inr_inl, one_apply]
    · rw [e23, h3, hypGram_inr_inl_inr_inr, Matrix.zero_apply]
    · rw [e31, h1', hypGram_inr_inr_inl, one_apply]
    · rw [e32, h3', hypGram_inr_inr_inr_inl, Matrix.zero_apply]
    · rw [e33, h4, hypGram_inr_inr_inr_inr, Matrix.zero_apply]

end Gram

section Blocks

variable (M : Matrix (HypIndex r ε) (HypIndex r ε) K)

@[expose] def blkA : Matrix (Fin r) (Fin r) K := of fun i j => M (.inl i) (.inl j)
@[expose] def blkX : Matrix (Fin r) (Fin ε) K := of fun i l => M (.inl i) (.inr (.inl l))
@[expose] def blkY : Matrix (Fin r) (Fin r) K := of fun i j => M (.inl i) (.inr (.inr j))
@[expose] def blkP : Matrix (Fin ε) (Fin ε) K := of fun k l => M (.inr (.inl k)) (.inr (.inl l))
@[expose] def blkQ : Matrix (Fin ε) (Fin r) K := of fun k j => M (.inr (.inl k)) (.inr (.inr j))
@[expose] def blkD : Matrix (Fin r) (Fin r) K :=
  of fun i j => M (.inr (.inr i)) (.inr (.inr j))

variable {M}

theorem eq_blk3_of_blockTriangular (hM : M.BlockTriangular fullPos) :
    M = blk3 (blkA M) (blkX M) (blkY M) (blkP M) (blkQ M) (blkD M) ∧
      (blkA M).IsUpperTriangular ∧ (blkP M).IsUpperTriangular ∧ (blkD M).IsLowerTriangular := by
  refine ⟨?_, fun i j hij => ?_, fun k l hkl => ?_, fun i j hij => ?_⟩
  · ext a b
    rcases a with ⟨i, hi⟩ | ⟨k, hk⟩ | ⟨i, hi⟩ <;> rcases b with ⟨j, hj⟩ | ⟨l, hl⟩ | ⟨j, hj⟩ <;>
      first
      | rfl
      | (rw [hM (by simp; omega)]; rfl)
  · exact hM (by simpa using hij)
  · exact hM (by simpa using hkl)
  · have := i.2
    have := j.2
    change i.1 < j.1 at hij
    exact hM (by simp only [fullPos_inr_inr]; omega)

theorem blockTriangular_blk3 {A : Matrix (Fin r) (Fin r) K} {P : Matrix (Fin ε) (Fin ε) K}
    {D : Matrix (Fin r) (Fin r) K} (hA : A.IsUpperTriangular) (hP : P.IsUpperTriangular)
    (hD : D.IsLowerTriangular) (X : Matrix (Fin r) (Fin ε) K) (Y : Matrix (Fin r) (Fin r) K)
    (Q : Matrix (Fin ε) (Fin r) K) : (blk3 A X Y P Q D).BlockTriangular fullPos := by
  intro a b hab
  rcases a with ⟨i, hi⟩ | ⟨k, hk⟩ | ⟨i, hi⟩ <;> rcases b with ⟨j, hj⟩ | ⟨l, hl⟩ | ⟨j, hj⟩ <;>
    simp only [fullPos_inl, fullPos_inr_inl, fullPos_inr_inr] at hab
  · exact hA (show (⟨j, hj⟩ : Fin r) < ⟨i, hi⟩ from hab)
  · omega
  · omega
  · rfl
  · exact hP (show (⟨l, hl⟩ : Fin ε) < ⟨k, hk⟩ by change l < k; omega)
  · omega
  · rfl
  · rfl
  · exact hD (show OrderDual.toDual (⟨j, hj⟩ : Fin r) < OrderDual.toDual ⟨i, hi⟩ by
      change i < j; omega)

end Blocks

open scoped Pointwise in
theorem mulVec_mem_orthogonal (h : UnitaryFieldData p f K) {g : hypSU h r ε}
    {W : Submodule K (HypIndex r ε → K)} (hW : g • W = W) {v : HypIndex r ε → K}
    (hv : v ∈ W.orthogonalBilin (hypForm h r ε)) :
    ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v ∈
      W.orthogonalBilin (hypForm h r ε) := by
  rw [Submodule.mem_orthogonalBilin] at hv ⊢
  intro u hu
  rw [← hW] at hu
  obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists u g W).mp hu
  change hypForm h r ε (g • w) (g • v) = 0
  rw [hypForm_smul_smul]
  exact hv w hw

theorem isoFlag_zero : isoFlag r ε K 0 = ⊥ := by
  rw [isoFlag_eq_posFlag (Nat.zero_le _), eq_bot_iff]
  intro v hv
  exact (Submodule.mem_bot K).mpr (funext fun a => hv a (Nat.zero_le _))

open scoped Pointwise in
theorem blockTriangular_of_mem_hypBorel (h : UnitaryFieldData p f K) (hε : ε ≤ 1)
    {g : hypSU h r ε} (hg : g ∈ hypBorel h r ε) :
    ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).BlockTriangular
      fullPos := by
  have hfix : ∀ j, j ≤ r → g • isoFlag r ε K j = isoFlag r ε K j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [isoFlag_zero, Subgroup.smul_def, smul_eq_map, Submodule.map_bot]
    · have hF := mem_hypBorel.mp hg j hj0 hj
      rwa [hypFlag, ite_eq_left hj] at hF
  rw [blockTriangular_fullPos_iff]
  intro i v hv
  by_cases hir : i ≤ r
  · rw [← isoFlag_eq_posFlag hir] at hv ⊢
    rw [← hfix i hir]
    exact Submodule.smul_mem_pointwise_smul v g _ hv
  · by_cases hin : i ≤ 2 * r + ε
    · have hj : 2 * r + ε - i ≤ r := by omega
      have heq : posFlag r ε K i =
          (isoFlag r ε K (2 * r + ε - i)).orthogonalBilin (hypForm h r ε) := by
        rw [orthogonal_isoFlag h hε hj]
        congr 1
        omega
      rw [heq] at hv ⊢
      exact mulVec_mem_orthogonal h (hfix _ hj) hv
    · intro a ha
      have := fullPos_lt a
      omega

section BarInvT

variable (h : UnitaryFieldData p f K)

@[expose] noncomputable def barInvT (A : Matrix (Fin r) (Fin r) K) : Matrix (Fin r) (Fin r) K :=
  ((A.map h.bar)⁻¹)ᵀ

variable {h}

theorem det_conjTranspose' (A : Matrix (Fin r) (Fin r) K) :
    ((A.map h.bar)ᵀ).det = h.bar A.det := by
  rw [det_transpose, RingHom.map_det]
  rfl

theorem isUnit_det_map {A : Matrix (Fin r) (Fin r) K} (hA : IsUnit A.det) :
    IsUnit (A.map h.bar).det := by
  rw [← det_transpose, det_conjTranspose']
  exact (hA.map h.bar)

theorem conjTranspose_mul_barInvT {A : Matrix (Fin r) (Fin r) K} (hA : IsUnit A.det) :
    (A.map h.bar)ᵀ * barInvT h A = 1 := by
  rw [barInvT, ← transpose_mul, nonsing_inv_mul _ (isUnit_det_map hA), transpose_one]

theorem conjTranspose_barInvT_mul {A : Matrix (Fin r) (Fin r) K} (hA : IsUnit A.det) :
    ((barInvT h A).map h.bar)ᵀ * A = 1 := by
  have := congrArg (fun M => (M.map h.bar)ᵀ) (conjTranspose_mul_barInvT (h := h) hA)
  simp only [conjTranspose_mul', conjTranspose_conjTranspose'] at this
  rw [this, Matrix.map_one _ (map_zero _) (map_one _), transpose_one]

theorem eq_barInvT_of_mul_eq_one {A D : Matrix (Fin r) (Fin r) K}
    (hAD : (A.map h.bar)ᵀ * D = 1) : D = barInvT h A := by
  rw [barInvT, transpose_nonsing_inv, inv_eq_right_inv hAD]

theorem isUnit_det_of_mul_eq_one {A D : Matrix (Fin r) (Fin r) K}
    (hAD : (A.map h.bar)ᵀ * D = 1) : IsUnit A.det := by
  have := congrArg det hAD
  rw [det_mul, det_conjTranspose', det_one] at this
  have h0 : h.bar A.det ≠ 0 := left_ne_zero_of_mul_eq_one this
  exact isUnit_iff_ne_zero.mpr fun h' => h0 (by rw [h', map_zero])

theorem det_barInvT {A : Matrix (Fin r) (Fin r) K} (hA : IsUnit A.det) :
    (barInvT h A).det = (h.bar A.det)⁻¹ := by
  have := congrArg det (conjTranspose_mul_barInvT (h := h) hA)
  rw [det_mul, det_conjTranspose', det_one] at this
  exact eq_inv_of_mul_eq_one_right this

theorem isLowerTriangular_barInvT {A : Matrix (Fin r) (Fin r) K} (hA : A.IsUpperTriangular)
    (hdet : IsUnit A.det) : (barInvT h A).IsLowerTriangular := by
  have hmap : (A.map h.bar).IsUpperTriangular := hA.map h.bar
  have := invertibleOfIsUnitDet _ (isUnit_det_map (h := h) hdet)
  exact (blockTriangular_inv_of_blockTriangular hmap).transpose

theorem barInvT_apply_self {A : Matrix (Fin r) (Fin r) K} (hA : A.IsUpperTriangular)
    (hdet : IsUnit A.det) (i : Fin r) : barInvT h A i i = (h.bar (A i i))⁻¹ := by
  have hmap : (A.map h.bar).IsUpperTriangular := hA.map h.bar
  have := invertibleOfIsUnitDet _ (isUnit_det_map (h := h) hdet)
  have hinv := blockTriangular_inv_of_blockTriangular hmap
  have h1 := mul_apply_self_of_blockTriangular (b := fun i : Fin r => (i : ℕ))
    (fun a b hab => Fin.ext hab) (M := A.map h.bar) (N := (A.map h.bar)⁻¹)
    (fun a b hab => hmap hab) (fun a b hab => hinv hab) i
  rw [mul_nonsing_inv _ (isUnit_det_map hdet), one_apply_eq, map_apply] at h1
  rw [barInvT, transpose_apply]
  exact (eq_inv_of_mul_eq_one_right h1.symm)

end BarInvT

theorem mem_hypBorel_iff_blockTriangular (h : UnitaryFieldData p f K) (hε : ε ≤ 1)
    (g : hypSU h r ε) :
    g ∈ hypBorel h r ε ↔
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).BlockTriangular
        fullPos :=
  ⟨blockTriangular_of_mem_hypBorel h hε, mem_hypBorel_of_blockTriangular h⟩

@[expose] noncomputable def mkHypSU (h : UnitaryFieldData p f K)
    (M : Matrix (HypIndex r ε) (HypIndex r ε) K)
    (hM : (M.map h.bar)ᵀ * hypGram r ε K * M = hypGram r ε K) (hdet : M.det = 1) : hypSU h r ε :=
  ⟨GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero), hM, hdet⟩

theorem coe_mkHypSU (h : UnitaryFieldData p f K) (M : Matrix (HypIndex r ε) (HypIndex r ε) K)
    (hM : (M.map h.bar)ᵀ * hypGram r ε K * M = hypGram r ε K) (hdet : M.det = 1) :
    (((mkHypSU h M hM hdet : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) = M :=
  rfl

theorem eq_zero_of_isEmpty_cols {m n : Type} [IsEmpty n] (X : Matrix m n K) : X = 0 :=
  Matrix.ext fun _ j => isEmptyElim j

theorem eq_zero_of_isEmpty_rows {m n : Type} [IsEmpty m] (X : Matrix m n K) : X = 0 :=
  Matrix.ext fun i _ => isEmptyElim i

section Even

variable (h : UnitaryFieldData p f K)

@[expose] noncomputable def evenMat (A C : Matrix (Fin r) (Fin r) K) :
    Matrix (HypIndex r 0) (HypIndex r 0) K :=
  blk3 A 0 (A * C) 0 0 (barInvT h A)

variable {h}

theorem evenMat_gram {A C : Matrix (Fin r) (Fin r) K} (hA : IsUnit A.det)
    (hC : C + (C.map h.bar)ᵀ = 0) :
    ((evenMat h A C).map h.bar)ᵀ * hypGram r 0 K * evenMat h A C = hypGram r 0 K := by
  refine (blk3_gram_iff h _ _ _ _ _ _).mpr ⟨conjTranspose_mul_barInvT hA,
    eq_zero_of_isEmpty_rows _ |>.trans (eq_zero_of_isEmpty_rows _).symm,
    eq_zero_of_isEmpty_rows _, ?_⟩
  rw [conjTranspose_mul', Matrix.mul_assoc, conjTranspose_mul_barInvT hA, Matrix.mul_one,
    eq_zero_of_isEmpty_rows (0 : Matrix (Fin 0) (Fin r) K), ← Matrix.mul_assoc,
    conjTranspose_barInvT_mul hA, Matrix.one_mul]
  simp only [Matrix.map_zero _ (map_zero h.bar), transpose_zero, Matrix.zero_mul, add_zero]
  rw [add_comm]
  exact hC

theorem det_evenMat {A : Matrix (Fin r) (Fin r) K} (hA : IsUnit A.det)
    (C : Matrix (Fin r) (Fin r) K) : (evenMat h A C).det = A.det / h.bar A.det := by
  rw [evenMat, det_blk3, show (0 : Matrix (Fin 0) (Fin 0) K).det = 1 from det_isEmpty, mul_one,
    det_barInvT hA, div_eq_mul_inv]

theorem exists_mem_hypBorel_evenMat {A C : Matrix (Fin r) (Fin r) K} (hA : A.IsUpperTriangular)
    (hdet : IsUnit A.det) (hC : C + (C.map h.bar)ᵀ = 0) (hd : A.det / h.bar A.det = 1) :
    ∃ g ∈ hypBorel h r 0, ((g : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) =
      evenMat h A C := by
  refine ⟨mkHypSU h _ (evenMat_gram hdet hC) (by rw [det_evenMat hdet, hd]),
    mem_hypBorel_of_blockTriangular h ?_, rfl⟩
  rw [coe_mkHypSU]
  exact blockTriangular_blk3 hA (fun k => isEmptyElim k) (isLowerTriangular_barInvT hA hdet) _ _ _

theorem exists_evenMat_of_mem_hypBorel {g : hypSU h r 0} (hg : g ∈ hypBorel h r 0) :
    ∃ A C : Matrix (Fin r) (Fin r) K, A.IsUpperTriangular ∧ IsUnit A.det ∧
      C + (C.map h.bar)ᵀ = 0 ∧ A.det / h.bar A.det = 1 ∧
      ((g : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) = evenMat h A C := by
  obtain ⟨M, hMg⟩ : ∃ M, ((g : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) =
      M := ⟨_, rfl⟩
  have hT := blockTriangular_of_mem_hypBorel h (by norm_num) hg
  rw [hMg] at hT
  obtain ⟨hM, hA, -, -⟩ := eq_blk3_of_blockTriangular hT
  have hgram := (mem_hypSU.mp g.2).1
  have hdetM := (mem_hypSU.mp g.2).2
  rw [hMg, hM] at hgram hdetM
  obtain ⟨h1, -, -, h4⟩ := (blk3_gram_iff h _ _ _ _ _ _).mp hgram
  have hdet := isUnit_det_of_mul_eq_one h1
  have hD := eq_barInvT_of_mul_eq_one h1
  set C := (blkA M)⁻¹ * blkY M with hC
  have hY : blkY M = blkA M * C := by rw [hC, mul_nonsing_inv_cancel_left _ _ hdet]
  refine ⟨blkA M, C, hA, hdet, ?_, ?_, ?_⟩
  · rw [hY, hD, conjTranspose_mul', Matrix.mul_assoc, conjTranspose_mul_barInvT hdet,
      Matrix.mul_one, ← Matrix.mul_assoc, conjTranspose_barInvT_mul hdet, Matrix.one_mul,
      eq_zero_of_isEmpty_rows (blkQ M), Matrix.map_zero _ (map_zero h.bar), transpose_zero,
      Matrix.zero_mul, add_zero] at h4
    rw [add_comm]
    exact h4
  · rw [det_blk3, show (blkP M).det = 1 from det_isEmpty, mul_one, hD, det_barInvT hdet,
      ← div_eq_mul_inv] at hdetM
    exact hdetM
  · rw [hMg]
    conv_lhs => rw [hM]
    rw [hY, hD, eq_zero_of_isEmpty_cols (blkX M), eq_zero_of_isEmpty_rows (blkP M),
      eq_zero_of_isEmpty_rows (blkQ M)]
    rfl

theorem barInvT_mul (A A' : Matrix (Fin r) (Fin r) K) :
    barInvT h (A * A') = barInvT h A * barInvT h A' := by
  rw [barInvT, barInvT, barInvT, Matrix.map_mul, Matrix.mul_inv_rev, transpose_mul]

theorem evenMat_mul {A C A' C' : Matrix (Fin r) (Fin r) K} (hA' : IsUnit A'.det) :
    evenMat h A C * evenMat h A' C' =
      evenMat h (A * A') (C' + A'⁻¹ * C * barInvT h A') := by
  rw [evenMat, evenMat, evenMat, blk3_mul, barInvT_mul]
  congr 1
  · simp
  · rw [Matrix.mul_add, Matrix.mul_assoc A A' C', ← Matrix.mul_assoc (A * A') (A'⁻¹ * C),
      Matrix.mul_assoc A A', mul_nonsing_inv_cancel_left _ _ hA', Matrix.zero_mul, add_zero,
      Matrix.mul_assoc A C]
  · simp

theorem evenMat_inj {A C A' C' : Matrix (Fin r) (Fin r) K} (hA : IsUnit A.det)
    (he : evenMat h A C = evenMat h A' C') : A = A' ∧ C = C' := by
  have hAA : A = A' := by
    ext i j
    exact congrFun (congrFun he (.inl i)) (.inl j)
  subst hAA
  refine ⟨rfl, ?_⟩
  have hY : A * C = A * C' := by
    ext i j
    exact congrFun (congrFun he (.inl i)) (.inr (.inr j))
  rw [← nonsing_inv_mul_cancel_left A C hA, hY, nonsing_inv_mul_cancel_left A C' hA]

end Even

section Odd

variable (h : UnitaryFieldData p f K)

@[expose] noncomputable def oddDiag (A : Matrix (Fin r) (Fin r) K) (d : K) :
    Matrix (HypIndex r 1) (HypIndex r 1) K :=
  blk3 A 0 0 (of fun _ _ => d) 0 (barInvT h A)

@[expose] noncomputable def oddUni (x : Fin r → K) (C : Matrix (Fin r) (Fin r) K) :
    Matrix (HypIndex r 1) (HypIndex r 1) K :=
  blk3 1 (replicateCol (Fin 1) x) C 1 (replicateRow (Fin 1) fun j => -h.bar (x j)) 1

variable {h}

theorem oddDiag_mul_oddUni (A : Matrix (Fin r) (Fin r) K) (d : K) (x : Fin r → K)
    (C : Matrix (Fin r) (Fin r) K) :
    oddDiag h A d * oddUni h x C = blk3 A (A * replicateCol (Fin 1) x) (A * C) (of fun _ _ => d)
      (of fun _ j => -d * h.bar (x j)) (barInvT h A) := by
  rw [oddDiag, oddUni, blk3_mul]
  congr 1
  · rw [Matrix.mul_one]
  · rw [Matrix.zero_mul, add_zero]
  · rw [Matrix.zero_mul, Matrix.zero_mul, add_zero, add_zero]
  · rw [Matrix.mul_one]
  · ext k j
    simp [mul_apply]
  · rw [Matrix.mul_one]

theorem conjTranspose_row_mul_row (x : Fin r → K) (d : K) (hd : h.bar d * d = 1) :
    (((of fun (_ : Fin 1) (j : Fin r) => -d * h.bar (x j)).map h.bar)ᵀ *
        of fun (_ : Fin 1) (j : Fin r) => -d * h.bar (x j)) =
      vecMulVec x fun j => h.bar (x j) := by
  ext i j
  simp only [mul_apply, transpose_apply, map_apply, of_apply, Finset.univ_unique,
    Finset.sum_singleton, map_mul, map_neg, h.bar_bar, vecMulVec_apply]
  linear_combination (x i * h.bar (x j)) * hd

theorem oddProd_gram {A C : Matrix (Fin r) (Fin r) K} {x : Fin r → K} {d : K} (hA : IsUnit A.det)
    (hd : h.bar d * d = 1) (hC : C + (C.map h.bar)ᵀ = -vecMulVec x fun j => h.bar (x j)) :
    ((oddDiag h A d * oddUni h x C).map h.bar)ᵀ * hypGram r 1 K * (oddDiag h A d * oddUni h x C) =
      hypGram r 1 K := by
  rw [oddDiag_mul_oddUni]
  refine (blk3_gram_iff h _ _ _ _ _ _).mpr ⟨conjTranspose_mul_barInvT hA, ?_, ?_, ?_⟩
  · ext k l
    simp [mul_apply, hd, one_apply, Subsingleton.elim k l]
  · rw [conjTranspose_mul', Matrix.mul_assoc, conjTranspose_mul_barInvT hA, Matrix.mul_one]
    ext k j
    simp only [Matrix.add_apply, mul_apply, transpose_apply, map_apply, replicateCol_apply,
      of_apply, Finset.univ_unique, Finset.sum_singleton, Matrix.zero_apply]
    linear_combination (-h.bar (x j)) * hd
  · rw [conjTranspose_mul', Matrix.mul_assoc, conjTranspose_mul_barInvT hA, Matrix.mul_one,
      ← Matrix.mul_assoc, conjTranspose_barInvT_mul hA, Matrix.one_mul,
      conjTranspose_row_mul_row x d hd, add_comm (C.map h.bar)ᵀ, add_assoc, add_comm _ C, hC,
      add_neg_cancel]

theorem det_oddProd {A : Matrix (Fin r) (Fin r) K} (hA : IsUnit A.det) (d : K) (x : Fin r → K)
    (C : Matrix (Fin r) (Fin r) K) :
    (oddDiag h A d * oddUni h x C).det = d * A.det / h.bar A.det := by
  rw [det_mul, oddDiag, oddUni, det_blk3, det_blk3, det_barInvT hA, det_one, det_one,
    det_fin_one, of_apply]
  field_simp

theorem bar_mul_self_of_eq_div {A : Matrix (Fin r) (Fin r) K} (hA : IsUnit A.det) {d : K}
    (hd : d = h.bar A.det / A.det) : h.bar d * d = 1 := by
  have h0 : A.det ≠ 0 := hA.ne_zero
  have h0' : h.bar A.det ≠ 0 := (map_ne_zero h.bar).mpr h0
  rw [hd, map_div₀, h.bar_bar]
  field_simp

theorem exists_mem_hypBorel_oddProd {A C : Matrix (Fin r) (Fin r) K} {x : Fin r → K} {d : K}
    (hA : A.IsUpperTriangular) (hdet : IsUnit A.det)
    (hC : C + (C.map h.bar)ᵀ = -vecMulVec x fun j => h.bar (x j)) (hd : d = h.bar A.det / A.det) :
    ∃ g ∈ hypBorel h r 1, ((g : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) =
      oddDiag h A d * oddUni h x C := by
  have hdd := bar_mul_self_of_eq_div hdet hd
  have hdet1 : (oddDiag h A d * oddUni h x C).det = 1 := by
    rw [det_oddProd hdet, hd]
    have h0 : A.det ≠ 0 := hdet.ne_zero
    have h0' : h.bar A.det ≠ 0 := (map_ne_zero h.bar).mpr h0
    field_simp
  refine ⟨mkHypSU h _ (oddProd_gram hdet hdd hC) hdet1,
    mem_hypBorel_of_blockTriangular h ?_, rfl⟩
  rw [coe_mkHypSU, oddDiag_mul_oddUni]
  exact blockTriangular_blk3 hA (fun k l hkl => absurd hkl (by simp [Subsingleton.elim k l]))
    (isLowerTriangular_barInvT hA hdet) _ _ _

theorem exists_oddProd_of_mem_hypBorel {g : hypSU h r 1} (hg : g ∈ hypBorel h r 1) :
    ∃ (A C : Matrix (Fin r) (Fin r) K) (x : Fin r → K) (d : K), A.IsUpperTriangular ∧
      IsUnit A.det ∧ C + (C.map h.bar)ᵀ = -vecMulVec x (fun j => h.bar (x j)) ∧
      d = h.bar A.det / A.det ∧
      ((g : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) =
        oddDiag h A d * oddUni h x C := by
  obtain ⟨M, hMg⟩ : ∃ M, ((g : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) =
      M := ⟨_, rfl⟩
  have hT := blockTriangular_of_mem_hypBorel h le_rfl hg
  rw [hMg] at hT
  obtain ⟨hM, hA, -, -⟩ := eq_blk3_of_blockTriangular hT
  have hgram := (mem_hypSU.mp g.2).1
  have hdetM := (mem_hypSU.mp g.2).2
  rw [hMg, hM] at hgram hdetM
  obtain ⟨h1, h2, h3, h4⟩ := (blk3_gram_iff h _ _ _ _ _ _).mp hgram
  have hdet := isUnit_det_of_mul_eq_one h1
  have hD := eq_barInvT_of_mul_eq_one h1
  set d := blkP M 0 0 with hd
  have hP : blkP M = of fun _ _ => d := by
    ext k l
    rw [Subsingleton.elim k 0, Subsingleton.elim l 0]
    rfl
  have hdd : h.bar d * d = 1 := by
    have := congrFun (congrFun h2 0) 0
    simpa [mul_apply, hP] using this
  set x : Fin r → K := fun i => ((blkA M)⁻¹ * blkX M) i 0 with hx
  have hX : blkX M = blkA M * replicateCol (Fin 1) x := by
    have : replicateCol (Fin 1) x = (blkA M)⁻¹ * blkX M := by
      ext i k
      rw [Subsingleton.elim k 0]
      rfl
    rw [this, mul_nonsing_inv_cancel_left _ _ hdet]
  set C := (blkA M)⁻¹ * blkY M with hC
  have hY : blkY M = blkA M * C := by rw [hC, mul_nonsing_inv_cancel_left _ _ hdet]
  have hQ : blkQ M = of fun _ j => -d * h.bar (x j) := by
    rw [hX, hD, conjTranspose_mul', Matrix.mul_assoc, conjTranspose_mul_barInvT hdet,
      Matrix.mul_one, hP] at h3
    ext k j
    rw [Subsingleton.elim k 0]
    have := congrFun (congrFun h3 0) j
    simp only [Matrix.add_apply, mul_apply, transpose_apply, map_apply, replicateCol_apply,
      of_apply, Finset.univ_unique, Finset.sum_singleton, Matrix.zero_apply] at this
    rw [of_apply]
    linear_combination d * this - blkQ M 0 j * hdd
  refine ⟨blkA M, C, x, d, hA, hdet, ?_, ?_, ?_⟩
  · rw [hY, hD, hQ, conjTranspose_mul', Matrix.mul_assoc, conjTranspose_mul_barInvT hdet,
      Matrix.mul_one, ← Matrix.mul_assoc, conjTranspose_barInvT_mul hdet, Matrix.one_mul,
      conjTranspose_row_mul_row x d hdd] at h4
    rw [eq_neg_iff_add_eq_zero, ← h4]
    abel
  · rw [det_blk3, hP, det_fin_one, of_apply, hD, det_barInvT hdet] at hdetM
    have h0 : (blkA M).det ≠ 0 := hdet.ne_zero
    have h0' : h.bar (blkA M).det ≠ 0 := (map_ne_zero h.bar).mpr h0
    field_simp at hdetM
    field_simp
    linear_combination hdetM
  · rw [hMg, oddDiag_mul_oddUni]
    conv_lhs => rw [hM]
    rw [← hX, ← hY, hP, hQ, hD]

theorem oddProd_inj {A C A' C' : Matrix (Fin r) (Fin r) K} {x x' : Fin r → K} {d d' : K}
    (hA : IsUnit A.det) (he : oddDiag h A d * oddUni h x C = oddDiag h A' d' * oddUni h x' C') :
    A = A' ∧ x = x' ∧ C = C' ∧ d = d' := by
  rw [oddDiag_mul_oddUni, oddDiag_mul_oddUni] at he
  have hAA : A = A' := by
    ext i j
    exact congrFun (congrFun he (.inl i)) (.inl j)
  subst hAA
  have hx : A * replicateCol (Fin 1) x = A * replicateCol (Fin 1) x' := by
    ext i k
    exact congrFun (congrFun he (.inl i)) (.inr (.inl k))
  have hY : A * C = A * C' := by
    ext i j
    exact congrFun (congrFun he (.inl i)) (.inr (.inr j))
  refine ⟨rfl, ?_, ?_, congrFun (congrFun he (.inr (.inl 0))) (.inr (.inl 0))⟩
  · have := congrArg (fun M => (A⁻¹ * M)) hx
    simp only [nonsing_inv_mul_cancel_left _ _ hA] at this
    funext i
    exact congrFun (congrFun this i) 0
  · rw [← nonsing_inv_mul_cancel_left A C hA, hY, nonsing_inv_mul_cancel_left A C' hA]

end Odd

@[expose] def IsUnitriangular (A : Matrix (Fin r) (Fin r) K) : Prop :=
  A.IsUpperTriangular ∧ ∀ i, A i i = 1

theorem IsUnitriangular.det_eq_one {A : Matrix (Fin r) (Fin r) K} (hA : IsUnitriangular A) :
    A.det = 1 := by
  rw [det_of_isUpperTriangular hA.1]
  exact Finset.prod_eq_one fun i _ => hA.2 i

theorem IsUnitriangular.isUnit_det {A : Matrix (Fin r) (Fin r) K} (hA : IsUnitriangular A) :
    IsUnit A.det := by
  rw [hA.det_eq_one]
  exact isUnit_one

variable {h : UnitaryFieldData p f K}

theorem mem_hypUnitriangular_iff_of_mem_hypBorel (hε : ε ≤ 1) {g : hypSU h r ε}
    (hg : g ∈ hypBorel h r ε) :
    g ∈ hypUnitriangular h r ε ↔
      ∀ a, ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a a = 1 :=
  ⟨fun hU => (mem_hypUnitriangular.mp hU).2, fun hd =>
    mem_hypUnitriangular.mpr ⟨blockTriangular_of_mem_hypBorel h hε hg, hd⟩⟩

@[expose] noncomputable def evenUnitriangularElt {A C : Matrix (Fin r) (Fin r) K}
    (hA : IsUnitriangular A) (hC : C + (C.map h.bar)ᵀ = 0) : hypUnitriangular h r 0 :=
  ⟨mkHypSU h (evenMat h A C) (evenMat_gram hA.isUnit_det hC)
      (by rw [det_evenMat hA.isUnit_det, hA.det_eq_one, map_one, div_one]),
    mem_hypUnitriangular.mpr ⟨blockTriangular_blk3 hA.1 (fun k => isEmptyElim k)
      (isLowerTriangular_barInvT hA.1 hA.isUnit_det) _ _ _, fun a => by
        rw [coe_mkHypSU]
        rcases a with i | k | i
        · exact hA.2 i
        · exact isEmptyElim k
        · rw [evenMat, blk3_inr_inr_inr_inr, barInvT_apply_self hA.1 hA.isUnit_det, hA.2 i,
            map_one, inv_one]⟩⟩

theorem coe_evenUnitriangularElt {A C : Matrix (Fin r) (Fin r) K} (hA : IsUnitriangular A)
    (hC : C + (C.map h.bar)ᵀ = 0) :
    ((((evenUnitriangularElt hA hC : hypUnitriangular h r 0) : hypSU h r 0) :
      GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) = evenMat h A C :=
  rfl

theorem exists_mem_hypUnitriangular_even_iff (M : Matrix (HypIndex r 0) (HypIndex r 0) K) :
    (∃ g ∈ hypUnitriangular h r 0,
        ((g : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) = M) ↔
      ∃ A C : Matrix (Fin r) (Fin r) K, IsUnitriangular A ∧ C + (C.map h.bar)ᵀ = 0 ∧
        M = evenMat h A C := by
  constructor
  · rintro ⟨g, hgU, rfl⟩
    have hgB := hypUnitriangular_le_hypBorel h hgU
    obtain ⟨A, C, hA, hdet, hC, -, hg⟩ := exists_evenMat_of_mem_hypBorel hgB
    refine ⟨A, C, ⟨hA, fun i => ?_⟩, hC, hg⟩
    have := (mem_hypUnitriangular.mp hgU).2 (.inl i)
    rwa [hg, evenMat, blk3_inl_inl] at this
  · rintro ⟨A, C, hA, hC, rfl⟩
    obtain ⟨g, hgB, hg⟩ := exists_mem_hypBorel_evenMat hA.1 hA.isUnit_det hC
      (by rw [hA.det_eq_one, map_one, div_one])
    refine ⟨g, (mem_hypUnitriangular_iff_of_mem_hypBorel (by norm_num) hgB).mpr fun a => ?_, hg⟩
    rw [hg]
    rcases a with i | k | i
    · exact hA.2 i
    · exact isEmptyElim k
    · rw [evenMat, blk3_inr_inr_inr_inr, barInvT_apply_self hA.1 hA.isUnit_det, hA.2 i, map_one,
        inv_one]

theorem exists_mem_hypUnitriangular_odd_iff (M : Matrix (HypIndex r 1) (HypIndex r 1) K) :
    (∃ g ∈ hypUnitriangular h r 1,
        ((g : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) = M) ↔
      ∃ (A C : Matrix (Fin r) (Fin r) K) (x : Fin r → K), IsUnitriangular A ∧
        C + (C.map h.bar)ᵀ = -vecMulVec x (fun j => h.bar (x j)) ∧
        M = oddDiag h A 1 * oddUni h x C := by
  constructor
  · rintro ⟨g, hgU, rfl⟩
    have hgB := hypUnitriangular_le_hypBorel h hgU
    obtain ⟨A, C, x, d, hA, hdet, hC, hd, hg⟩ := exists_oddProd_of_mem_hypBorel hgB
    have hA1 : ∀ i, A i i = 1 := fun i => by
      have := (mem_hypUnitriangular.mp hgU).2 (.inl i)
      rwa [hg, oddDiag_mul_oddUni, blk3_inl_inl] at this
    have hd1 : d = 1 := by
      rw [hd, IsUnitriangular.det_eq_one ⟨hA, hA1⟩, map_one, div_one]
    exact ⟨A, C, x, ⟨hA, hA1⟩, hC, by rw [hg, hd1]⟩
  · rintro ⟨A, C, x, hA, hC, rfl⟩
    obtain ⟨g, hgB, hg⟩ := exists_mem_hypBorel_oddProd hA.1 hA.isUnit_det hC
      (by rw [hA.det_eq_one, map_one, div_one])
    refine ⟨g, (mem_hypUnitriangular_iff_of_mem_hypBorel le_rfl hgB).mpr fun a => ?_, hg⟩
    rw [hg, oddDiag_mul_oddUni]
    rcases a with i | k | i
    · exact hA.2 i
    · rw [blk3_inr_inl_inr_inl, of_apply]
    · rw [blk3_inr_inr_inr_inr, barInvT_apply_self hA.1 hA.isUnit_det, hA.2 i, map_one, inv_one]

theorem diag_ne_zero_of_mem_hypBorel (hε : ε ≤ 1) {g : hypSU h r ε} (hg : g ∈ hypBorel h r ε)
    (a : HypIndex r ε) :
    ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a a ≠ 0 := by
  have hT := blockTriangular_of_mem_hypBorel h hε hg
  have h1 := mul_apply_self_of_blockTriangular fullPos_injective hT
    (blockTriangular_inv_fullPos hT) a
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_apply_eq] at h1
  exact left_ne_zero_of_mul_eq_one h1.symm

@[expose] noncomputable def hypDiagHom (h : UnitaryFieldData p f K) (r ε : ℕ) (hε : ε ≤ 1) :
    hypBorel h r ε →* (Fin r → Kˣ) where
  toFun g i := Units.mk0 ((((g : hypSU h r ε) : GL (HypIndex r ε) K) :
    Matrix (HypIndex r ε) (HypIndex r ε) K) (.inl i) (.inl i))
    (diag_ne_zero_of_mem_hypBorel hε g.2 _)
  map_one' := by
    funext i
    exact Units.ext (by simp)
  map_mul' g g' := by
    funext i
    refine Units.ext ?_
    simp only [Subgroup.coe_mul, Units.val_mul, Units.val_mk0, Pi.mul_apply]
    exact mul_apply_self_of_blockTriangular fullPos_injective
      (blockTriangular_of_mem_hypBorel h hε g.2) (blockTriangular_of_mem_hypBorel h hε g'.2) _

theorem coe_hypDiagHom (hε : ε ≤ 1) (g : hypBorel h r ε) (i : Fin r) :
    (hypDiagHom h r ε hε g i : K) = (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) (.inl i) (.inl i) :=
  rfl

theorem ker_hypDiagHom (hε : ε ≤ 1) :
    (hypDiagHom h r ε hε).ker = (hypUnitriangular h r ε).subgroupOf (hypBorel h r ε) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
    mem_hypUnitriangular_iff_of_mem_hypBorel hε g.2]
  have hdiag : (hypDiagHom h r ε hε g = 1) ↔ ∀ i, (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) (.inl i) (.inl i) = 1 := by
    rw [funext_iff]
    exact forall_congr' fun i => by rw [Units.ext_iff, coe_hypDiagHom, Pi.one_apply, Units.val_one]
  rw [hdiag]
  refine ⟨fun hA => ?_, fun hd i => hd _⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · obtain ⟨A, C, hAt, hdet, -, -, hg⟩ := exists_evenMat_of_mem_hypBorel g.2
    rw [hg] at hA ⊢
    intro a
    rcases a with i | k | i
    · exact hA i
    · exact isEmptyElim k
    · have hAi : A i i = 1 := hA i
      rw [evenMat, blk3_inr_inr_inr_inr, barInvT_apply_self hAt hdet, hAi, map_one, inv_one]
  · obtain ⟨A, C, x, d, hAt, hdet, -, hd, hg⟩ := exists_oddProd_of_mem_hypBorel g.2
    rw [hg, oddDiag_mul_oddUni] at hA ⊢
    have hA' : ∀ i, A i i = 1 := hA
    intro a
    rcases a with i | k | i
    · exact hA i
    · rw [blk3_inr_inl_inr_inl, of_apply, hd, IsUnitriangular.det_eq_one ⟨hAt, hA'⟩, map_one,
        div_one]
    · rw [blk3_inr_inr_inr_inr, barInvT_apply_self hAt hdet, hA' i, map_one, inv_one]

@[expose] noncomputable def ratioHom (h : UnitaryFieldData p f K) (r : ℕ) :
    (Fin r → Kˣ) →* Kˣ where
  toFun a := ∏ i, a i * (Units.map (h.bar : K →* K) (a i))⁻¹
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Pi.mul_apply, map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

theorem coe_ratioHom (a : Fin r → Kˣ) :
    (ratioHom h r a : K) = ∏ i, (a i : K) / h.bar (a i) := by
  simp [ratioHom, div_eq_mul_inv]

@[expose] noncomputable def evenDiagGroup (h : UnitaryFieldData p f K) (r : ℕ) :
    Subgroup (Fin r → Kˣ) :=
  (ratioHom h r).ker

theorem mem_evenDiagGroup {a : Fin r → Kˣ} :
    a ∈ evenDiagGroup h r ↔ ∏ i, (a i : K) / h.bar (a i) = 1 := by
  rw [evenDiagGroup, MonoidHom.mem_ker, Units.ext_iff, coe_ratioHom, Units.val_one]

theorem range_ratioHom (hr : 1 ≤ r) : (ratioHom h r).range = (Units.map h.normHom).ker := by
  ext u
  rw [MonoidHom.mem_range, UnitaryFieldData.mem_ker_normUnits]
  constructor
  · rintro ⟨a, rfl⟩
    rw [coe_ratioHom]
    induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
    | empty => simp [UnitaryFieldData.norm]
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, CFSG.ClassicalGroups.UnitaryFlag.norm_mul_eq h, ih, mul_one]
      exact h.norm_div_bar (a i).ne_zero
  · intro hu
    obtain ⟨c, hc0, hc⟩ := h.exists_div_bar_eq hu
    refine ⟨Pi.mulSingle ⟨0, hr⟩ (Units.mk0 c hc0), Units.ext ?_⟩
    rw [coe_ratioHom, Finset.prod_eq_single ⟨0, hr⟩]
    · simp [hc]
    · intro j _ hj
      simp [Pi.mulSingle_eq_of_ne hj]
    · simp

theorem exists_mem_hypBorel_diag {a : Fin r → Kˣ} {d : Fin ε → Kˣ}
    (hd : ∀ k, h.norm (d k : K) = 1) (hp : torusRatio h a d = 1) (hε : ε ≤ 1) :
    ∃ g : hypBorel h r ε, hypDiagHom h r ε hε g = a := by
  obtain ⟨g, hgT, hg⟩ := torusMat_mem_hypSU h a hd hp
  refine ⟨⟨g, hypTorus_le_hypBorel h hgT⟩, funext fun i => Units.ext ?_⟩
  rw [coe_hypDiagHom]
  change ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) (.inl i) (.inl i) = _
  rw [hg, diagonal_apply_eq]
  rfl

theorem range_hypDiagHom_even : (hypDiagHom h r 0 (Nat.zero_le 1)).range = evenDiagGroup h r := by
  ext a
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨A, C, hA, hdet, -, hd, hg⟩ := exists_evenMat_of_mem_hypBorel g.2
    rw [mem_evenDiagGroup]
    simp only [coe_hypDiagHom, hg, evenMat, blk3_inl_inl]
    rw [Finset.prod_div_distrib, ← map_prod, ← det_of_isUpperTriangular hA]
    exact hd
  · intro ha
    refine exists_mem_hypBorel_diag (d := isEmptyElim) (fun k => isEmptyElim k) ?_ _
    rw [torusRatio, ← coe_ratioHom, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    rw [evenDiagGroup, MonoidHom.mem_ker] at ha
    rw [ha, Units.val_one]

theorem range_hypDiagHom_odd (hr : 1 ≤ r) : (hypDiagHom h r 1 le_rfl).range = ⊤ := by
  refine eq_top_iff.mpr fun a _ => ?_
  have hnorm : h.norm ((ratioHom h r a)⁻¹ : Kˣ) = 1 := by
    have : ratioHom h r a ∈ (Units.map h.normHom).ker := by
      rw [← range_ratioHom hr]
      exact ⟨a, rfl⟩
    rw [UnitaryFieldData.mem_ker_normUnits] at this
    rw [Units.val_inv_eq_inv_val, norm_inv_eq h, this, inv_one]
  refine exists_mem_hypBorel_diag (d := fun _ => (ratioHom h r a)⁻¹) (fun _ => hnorm) ?_ le_rfl
  rw [torusRatio, ← coe_ratioHom, Fin.prod_univ_one, ← Units.val_mul, mul_inv_cancel,
    Units.val_one]

theorem card_fun_units (h : UnitaryFieldData p f K) (r : ℕ) :
    Nat.card (Fin r → Kˣ) = ((p ^ f) ^ 2 - 1) ^ r := by
  have := h.finite
  rw [Nat.card_fun, Nat.card_units, h.card_eq_sq, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_evenDiagGroup (hr : 1 ≤ r) :
    Nat.card (evenDiagGroup h r) = ((p ^ f) ^ 2 - 1) ^ r / (p ^ f + 1) := by
  have := h.finite
  have h1 := Subgroup.card_mul_index (ratioHom h r).ker
  rw [Subgroup.index_ker, range_ratioHom hr, h.card_ker_normUnits_and_surjective.1,
    card_fun_units h] at h1
  rw [evenDiagGroup, ← h1, Nat.mul_div_cancel _ (Nat.succ_pos _)]

theorem normal_hypUnitriangular (hε : ε ≤ 1) :
    ((hypUnitriangular h r ε).subgroupOf (hypBorel h r ε)).Normal := by
  rw [← ker_hypDiagHom hε]
  infer_instance

theorem card_quotient_hypUnitriangular (hε : ε ≤ 1) :
    Nat.card (hypBorel h r ε ⧸ (hypUnitriangular h r ε).subgroupOf (hypBorel h r ε)) =
      Nat.card (hypDiagHom h r ε hε).range := by
  change ((hypUnitriangular h r ε).subgroupOf (hypBorel h r ε)).index = _
  rw [← ker_hypDiagHom hε, Subgroup.index_ker]

theorem unitary_triangular_structure (h : UnitaryFieldData p f K) (hr : 1 ≤ r) :
    (∀ ε (hε : ε ≤ 1),
      (∀ g : hypSU h r ε, g ∈ hypBorel h r ε ↔
        ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).BlockTriangular
          fullPos) ∧
      (∀ g : hypSU h r ε, g ∈ hypUnitriangular h r ε ↔
        ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).BlockTriangular
          fullPos ∧
          ∀ a, ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a a = 1) ∧
      (∀ (g : hypBorel h r ε) (i : Fin r), (hypDiagHom h r ε hε g i : K) =
        (((g : hypSU h r ε) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)
          (.inl i) (.inl i)) ∧
      (hypDiagHom h r ε hε).ker = (hypUnitriangular h r ε).subgroupOf (hypBorel h r ε) ∧
      ((hypUnitriangular h r ε).subgroupOf (hypBorel h r ε)).Normal) ∧
    (∀ M : Matrix (HypIndex r 0) (HypIndex r 0) K,
      (∃ g ∈ hypBorel h r 0,
        ((g : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) = M) ↔
      ∃ A C : Matrix (Fin r) (Fin r) K, A.IsUpperTriangular ∧ IsUnit A.det ∧
        C + (C.map h.bar)ᵀ = 0 ∧ A.det / h.bar A.det = 1 ∧ M = evenMat h A C) ∧
    (∀ A C A' C' : Matrix (Fin r) (Fin r) K, IsUnit A.det →
      evenMat h A C = evenMat h A' C' → A = A' ∧ C = C') ∧
    (∀ M : Matrix (HypIndex r 0) (HypIndex r 0) K,
      (∃ g ∈ hypUnitriangular h r 0,
        ((g : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) = M) ↔
      ∃ A C : Matrix (Fin r) (Fin r) K, IsUnitriangular A ∧ C + (C.map h.bar)ᵀ = 0 ∧
        M = evenMat h A C) ∧
    (hypDiagHom h r 0 (Nat.zero_le 1)).range = evenDiagGroup h r ∧
    (∀ a : Fin r → Kˣ, a ∈ evenDiagGroup h r ↔ ∏ i, (a i : K) / h.bar (a i) = 1) ∧
    Nat.card (hypBorel h r 0 ⧸ (hypUnitriangular h r 0).subgroupOf (hypBorel h r 0)) =
      ((p ^ f) ^ 2 - 1) ^ r / (p ^ f + 1) ∧
    (∀ M : Matrix (HypIndex r 1) (HypIndex r 1) K,
      (∃ g ∈ hypBorel h r 1,
        ((g : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) = M) ↔
      ∃ (A C : Matrix (Fin r) (Fin r) K) (x : Fin r → K) (d : K), A.IsUpperTriangular ∧
        IsUnit A.det ∧ C + (C.map h.bar)ᵀ = -vecMulVec x (fun j => h.bar (x j)) ∧
        d = h.bar A.det / A.det ∧ M = oddDiag h A d * oddUni h x C) ∧
    (∀ (A C A' C' : Matrix (Fin r) (Fin r) K) (x x' : Fin r → K) (d d' : K), IsUnit A.det →
      oddDiag h A d * oddUni h x C = oddDiag h A' d' * oddUni h x' C' →
        A = A' ∧ x = x' ∧ C = C' ∧ d = d') ∧
    (∀ M : Matrix (HypIndex r 1) (HypIndex r 1) K,
      (∃ g ∈ hypUnitriangular h r 1,
        ((g : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) = M) ↔
      ∃ (A C : Matrix (Fin r) (Fin r) K) (x : Fin r → K), IsUnitriangular A ∧
        C + (C.map h.bar)ᵀ = -vecMulVec x (fun j => h.bar (x j)) ∧
        M = oddDiag h A 1 * oddUni h x C) ∧
    (hypDiagHom h r 1 le_rfl).range = ⊤ ∧
    Nat.card (hypBorel h r 1 ⧸ (hypUnitriangular h r 1).subgroupOf (hypBorel h r 1)) =
      ((p ^ f) ^ 2 - 1) ^ r := by
  refine ⟨fun ε hε => ⟨mem_hypBorel_iff_blockTriangular h hε, fun g => mem_hypUnitriangular,
      coe_hypDiagHom hε, ker_hypDiagHom hε, normal_hypUnitriangular hε⟩,
    fun M => ⟨?_, ?_⟩, fun A C A' C' hA he => evenMat_inj hA he,
    exists_mem_hypUnitriangular_even_iff, range_hypDiagHom_even, fun a => mem_evenDiagGroup, ?_,
    fun M => ⟨?_, ?_⟩, fun A C A' C' x x' d d' hA he => oddProd_inj hA he,
    exists_mem_hypUnitriangular_odd_iff, range_hypDiagHom_odd hr, ?_⟩
  · rintro ⟨g, hg, rfl⟩
    exact exists_evenMat_of_mem_hypBorel hg
  · rintro ⟨A, C, hA, hdet, hC, hd, rfl⟩
    exact exists_mem_hypBorel_evenMat hA hdet hC hd
  · rw [card_quotient_hypUnitriangular (Nat.zero_le 1), range_hypDiagHom_even,
      card_evenDiagGroup hr]
  · rintro ⟨g, hg, rfl⟩
    exact exists_oddProd_of_mem_hypBorel hg
  · rintro ⟨A, C, x, d, hA, hdet, hC, hd, rfl⟩
    exact exists_mem_hypBorel_oddProd hA hdet hC hd
  · rw [card_quotient_hypUnitriangular le_rfl, range_hypDiagHom_odd hr, Subgroup.card_top,
      card_fun_units h]

end CFSG.ClassicalGroups.UnitaryFlag
