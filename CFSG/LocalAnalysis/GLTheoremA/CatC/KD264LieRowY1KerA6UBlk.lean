module

public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def blkE :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K ≃ₐ[K] Matrix (Fin 6) (Fin 6) K :=
  Matrix.reindexAlgEquiv K K finSumFinEquiv

@[expose] noncomputable def blk (A B C D : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 6) (Fin 6) K :=
  blkE (Matrix.fromBlocks A B C D)

theorem blk_mul (A B C D A' B' C' D' : Matrix (Fin 3) (Fin 3) K) :
    blk A B C D * blk A' B' C' D' =
      blk (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  unfold blk
  rw [← map_mul, Matrix.fromBlocks_multiply]

theorem blk_one : blk (1 : Matrix (Fin 3) (Fin 3) K) 0 0 1 = 1 := by
  unfold blk
  rw [Matrix.fromBlocks_one]
  exact map_one blkE

theorem blk_transpose (A B C D : Matrix (Fin 3) (Fin 3) K) :
    (blk A B C D)ᵀ = blk Aᵀ Cᵀ Bᵀ Dᵀ := by
  unfold blk blkE
  rw [Matrix.reindexAlgEquiv_apply, Matrix.reindexAlgEquiv_apply, Matrix.transpose_reindex,
    Matrix.fromBlocks_transpose]

theorem blk_map (g : K →+* K) (A B C D : Matrix (Fin 3) (Fin 3) K) :
    (blk A B C D).map g = blk (A.map g) (B.map g) (C.map g) (D.map g) := by
  unfold blk blkE
  rw [Matrix.reindexAlgEquiv_apply, Matrix.reindexAlgEquiv_apply]
  ext i j
  rcases hi : (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm i with a | a <;>
    rcases hj : (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm j with b | b <;>
    simp [Matrix.reindex_apply, Matrix.map_apply, hi, hj]

theorem det_blk_diag (A D : Matrix (Fin 3) (Fin 3) K) :
    (blk A 0 0 D).det = A.det * D.det := by
  unfold blk blkE
  rw [Matrix.reindexAlgEquiv_apply, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

@[expose] noncomputable def hypJ : Matrix (Fin 6) (Fin 6) K := blk 0 1 1 0

theorem bar_bar_of (h : UnitaryFieldData p f K) (x : K) : h.bar (h.bar x) = x := by
  classical
  have hfin : Finite K := h.finite
  haveI := Fintype.ofFinite K
  have hcard : Fintype.card K = p ^ (2 * f) := by
    rw [← Nat.card_eq_fintype_card]
    exact h.card
  have e : p ^ f * p ^ f = Fintype.card K := by
    rw [hcard, ← pow_add, two_mul]
  rw [UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply, ← pow_mul, e]
  exact FiniteField.pow_card x

theorem GL_mul_inv_mat (A : GL (Fin 3) K) :
    (A : Matrix (Fin 3) (Fin 3) K) * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 :=
  Units.mul_inv A

theorem GL_inv_mul_mat (A : GL (Fin 3) K) :
    ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) = 1 :=
  Units.inv_mul A

theorem map_zero_bar (h : UnitaryFieldData p f K) :
    (0 : Matrix (Fin 3) (Fin 3) K).map h.bar = 0 :=
  Matrix.map_zero _ (map_zero _)

theorem map_one_bar (h : UnitaryFieldData p f K) :
    (1 : Matrix (Fin 3) (Fin 3) K).map h.bar = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem blk_diag_mul (X X' Y Y' : Matrix (Fin 3) (Fin 3) K) :
    blk X 0 0 Y * blk X' 0 0 Y' = blk (X * X') 0 0 (Y * Y') := by
  rw [blk_mul]
  simp only [mul_zero, zero_mul, add_zero, zero_add]

@[expose] noncomputable def lowBlk (h : UnitaryFieldData p f K) (A : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K :=
  (((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ

theorem lowBlk_mul_upper (h : UnitaryFieldData p f K) (A : GL (Fin 3) K) :
    lowBlk h A * ((A : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ = 1 := by
  unfold lowBlk
  rw [← Matrix.transpose_mul, ← Matrix.map_mul, GL_mul_inv_mat, map_one_bar h, transpose_one]

theorem upper_mul_lowBlk (h : UnitaryFieldData p f K) (A : GL (Fin 3) K) :
    ((A : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * lowBlk h A = 1 := by
  unfold lowBlk
  rw [← Matrix.transpose_mul, ← Matrix.map_mul, GL_inv_mul_mat, map_one_bar h, transpose_one]

@[expose] noncomputable def Mh (h : UnitaryFieldData p f K) (A : GL (Fin 3) K) : GL (Fin 6) K :=
  ⟨blk (A : Matrix (Fin 3) (Fin 3) K) 0 0 (lowBlk h A),
    blk ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0
      ((A : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ,
    by rw [blk_diag_mul, GL_mul_inv_mat, lowBlk_mul_upper h, blk_one],
    by rw [blk_diag_mul, GL_inv_mul_mat, upper_mul_lowBlk h, blk_one]⟩

theorem Mh_val (h : UnitaryFieldData p f K) (A : GL (Fin 3) K) :
    ((Mh h A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      blk (A : Matrix (Fin 3) (Fin 3) K) 0 0 (lowBlk h A) := rfl

theorem lowBlk_map_bar (h : UnitaryFieldData p f K) (A : GL (Fin 3) K) :
    ((lowBlk h A).map h.bar)ᵀ = ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  simp [lowBlk, bar_bar_of]

theorem lowBlk_mul (h : UnitaryFieldData p f K) (A B : GL (Fin 3) K) :
    lowBlk h (A * B) = lowBlk h A * lowBlk h B := by
  unfold lowBlk
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]

theorem Mh_mul (h : UnitaryFieldData p f K) (A B : GL (Fin 3) K) :
    Mh h (A * B) = Mh h A * Mh h B := by
  apply Units.ext
  show blk ((A * B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 (lowBlk h (A * B)) =
    blk (A : Matrix (Fin 3) (Fin 3) K) 0 0 (lowBlk h A) * blk (B : Matrix (Fin 3) (Fin 3) K) 0 0
      (lowBlk h B)
  rw [blk_diag_mul, lowBlk_mul, Units.val_mul]

theorem det_lowBlk (h : UnitaryFieldData p f K) (A : GL (Fin 3) K) :
    (lowBlk h A).det = h.bar ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det := by
  unfold lowBlk
  rw [Matrix.det_transpose]
  exact (RingHom.map_det h.bar _).symm

theorem Mh_mem (h : UnitaryFieldData p f K) (A : GL (Fin 3) K) (hA : (A : Matrix (Fin 3) (Fin 3) K).det = 1) :
    Mh h A ∈ gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K) := by
  rw [mem_gramSU]
  have hdet : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have h1 := congrArg Matrix.det (GL_inv_mul_mat A)
    rw [Matrix.det_mul, hA, mul_one, Matrix.det_one] at h1
    exact h1
  refine ⟨?_, ?_⟩
  · have hv : ((Mh h A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        blk (A : Matrix (Fin 3) (Fin 3) K) 0 0 (lowBlk h A) := rfl
    have hY : ((A : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * lowBlk h A = 1 :=
      upper_mul_lowBlk h A
    have hZ : ((lowBlk h A).map h.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [lowBlk_map_bar h A, GL_inv_mul_mat A]
    rw [hv, blk_map, blk_transpose, hypJ, blk_mul, blk_mul]
    simp only [map_zero_bar h, transpose_zero, mul_zero, zero_mul, add_zero, zero_add, mul_one,
      hY, hZ]
  · show (blk (A : Matrix (Fin 3) (Fin 3) K) 0 0 (lowBlk h A)).det = 1
    rw [det_blk_diag, det_lowBlk, hdet, map_one, mul_one]
    exact hA

@[expose] def ie (k : Fin 3) : Fin 6 := (finSumFinEquiv (Sum.inl k) : Fin (3 + 3))

@[expose] def jf (k : Fin 3) : Fin 6 := (finSumFinEquiv (Sum.inr k) : Fin (3 + 3))

theorem blk_apply (A B C D : Matrix (Fin 3) (Fin 3) K) (a b : Fin 6) :
    blk A B C D a b = Matrix.fromBlocks A B C D ((finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm a)
      ((finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm b) := by
  unfold blk blkE
  rw [Matrix.reindexAlgEquiv_apply]
  rfl

theorem blk_ll (A B C D : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    blk A B C D (ie i) (ie j) = A i j := by
  rw [blk_apply, ie, ie]
  simp

theorem blk_lr (A B C D : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    blk A B C D (ie i) (jf j) = B i j := by
  rw [blk_apply, ie, jf]
  simp

theorem blk_rl (A B C D : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    blk A B C D (jf i) (ie j) = C i j := by
  rw [blk_apply, ie, jf]
  simp

theorem blk_rr (A B C D : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    blk A B C D (jf i) (jf j) = D i j := by
  rw [blk_apply, jf, jf]
  simp

theorem eq_blk_of (M : Matrix (Fin 6) (Fin 6) K) :
    M = blk (Matrix.of fun i j => M (ie i) (ie j)) (Matrix.of fun i j => M (ie i) (jf j))
      (Matrix.of fun i j => M (jf i) (ie j)) (Matrix.of fun i j => M (jf i) (jf j)) := by
  ext a b
  rcases ha : (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm a with i | i <;>
    rcases hb : (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm b with j | j
  · have ha' : a = ie i := by rw [ie, ← ha]; simp
    have hb' : b = ie j := by rw [ie, ← hb]; simp
    subst ha' hb'
    rw [blk_ll]; rfl
  · have ha' : a = ie i := by rw [ie, ← ha]; simp
    have hb' : b = jf j := by rw [jf, ← hb]; simp
    subst ha' hb'
    rw [blk_lr]; rfl
  · have ha' : a = jf i := by rw [jf, ← ha]; simp
    have hb' : b = ie j := by rw [ie, ← hb]; simp
    subst ha' hb'
    rw [blk_rl]; rfl
  · have ha' : a = jf i := by rw [jf, ← ha]; simp
    have hb' : b = jf j := by rw [jf, ← hb]; simp
    subst ha' hb'
    rw [blk_rr]; rfl

theorem blk_inj {A B C D A' B' C' D' : Matrix (Fin 3) (Fin 3) K}
    (h : blk A B C D = blk A' B' C' D') : A = A' ∧ B = B' ∧ C = C' ∧ D = D' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    have := congrFun (congrFun h (ie i)) (ie j)
    rwa [blk_ll, blk_ll] at this
  · ext i j
    have := congrFun (congrFun h (ie i)) (jf j)
    rwa [blk_lr, blk_lr] at this
  · ext i j
    have := congrFun (congrFun h (jf i)) (ie j)
    rwa [blk_rl, blk_rl] at this
  · ext i j
    have := congrFun (congrFun h (jf i)) (jf j)
    rwa [blk_rr, blk_rr] at this

theorem hyp_block_isometry (h : UnitaryFieldData p f K) (P S : Matrix (Fin 3) (Fin 3) K)
    (hx : ((blk P 0 0 S).map h.bar)ᵀ * hypJ * blk P 0 0 S = hypJ) :
    (P.map h.bar)ᵀ * S = 1 := by
  rw [blk_map, blk_transpose, hypJ, blk_mul, blk_mul] at hx
  simp only [Matrix.map_zero, transpose_zero, mul_zero, zero_mul, add_zero, zero_add, mul_one] at hx
  exact (blk_inj hx).2.1

theorem ie_injective : Function.Injective (ie : Fin 3 → Fin 6) :=
  finSumFinEquiv.injective.comp Sum.inl_injective

theorem jf_injective : Function.Injective (jf : Fin 3 → Fin 6) :=
  finSumFinEquiv.injective.comp Sum.inr_injective

theorem ie_ne_jf (k l : Fin 3) : ie k ≠ jf l := by
  intro h
  have := finSumFinEquiv.injective h
  exact Sum.inl_ne_inr this

theorem diag_blk (d : Fin 6 → K) :
    Matrix.diagonal d = blk (Matrix.diagonal fun k => d (ie k)) 0 0
      (Matrix.diagonal fun k => d (jf k)) := by
  ext i j
  rcases hi : (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm i with k | k <;>
    rcases hj : (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm j with l | l
  · have hi' : i = ie k := by rw [ie, ← hi]; simp
    have hj' : j = ie l := by rw [ie, ← hj]; simp
    subst hi' hj'
    rw [blk_ll, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases hkl : k = l
    · subst hkl; simp
    · simp [hkl, ie_injective.ne hkl]
  · have hi' : i = ie k := by rw [ie, ← hi]; simp
    have hj' : j = jf l := by rw [jf, ← hj]; simp
    subst hi' hj'
    rw [blk_lr]
    simp [Matrix.diagonal_apply, ie_ne_jf, Matrix.zero_apply]
  · have hi' : i = jf k := by rw [jf, ← hi]; simp
    have hj' : j = ie l := by rw [ie, ← hj]; simp
    subst hi' hj'
    rw [blk_rl]
    simp [Matrix.diagonal_apply, Ne.symm (ie_ne_jf l k), Matrix.zero_apply]
  · have hi' : i = jf k := by rw [jf, ← hi]; simp
    have hj' : j = jf l := by rw [jf, ← hj]; simp
    subst hi' hj'
    rw [blk_rr, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases hkl : k = l
    · subst hkl; simp
    · simp [hkl, jf_injective.ne hkl]




end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
