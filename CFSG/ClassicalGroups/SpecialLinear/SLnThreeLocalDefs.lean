module

public import CFSG.Open.StatedAPI

public section

namespace CFSG.ClassicalGroups.SLnThreeLocal

open Matrix CFSG.Open

variable {K : Type} [Field K] {n : ℕ}

@[expose] def blockS (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, -1]

theorem blockS_mul_self : blockS K * blockS K = !![-1, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockS, Matrix.mul_apply, Fin.sum_univ_two]

theorem blockS_mul_blockS_mul : blockS K * (blockS K * blockS K) = 1 := by
  rw [blockS_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockS, Matrix.mul_apply, Fin.sum_univ_two]

theorem blockS_mul_mul_blockS : blockS K * blockS K * blockS K = 1 := by
  rw [blockS_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockS, Matrix.mul_apply, Fin.sum_univ_two]

theorem blockS_pow_three : blockS K ^ 3 = 1 := by
  rw [pow_succ, pow_two]
  exact blockS_mul_mul_blockS

theorem det_blockS : (blockS K).det = 1 := by
  simp [blockS, Matrix.det_fin_two]

theorem blockS_ne_one : blockS K ≠ 1 := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [blockS] at this

theorem blockS_mul_self_ne_one : blockS K * blockS K ≠ 1 := by
  intro h
  rw [blockS_mul_self] at h
  have := congrFun (congrFun h 0) 1
  simp at this

theorem blockS_mulVec_ne_self : blockS K *ᵥ ![1, 0] ≠ ![1, 0] := by
  intro h
  have := congrFun h 0
  simp [blockS, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this

theorem zmod_three_eq_one_or_two {k : ZMod 3} (hk : k ≠ 0) : k = 1 ∨ k = 2 := by
  revert k; decide

@[expose] def blockSGL (K : Type) [Field K] : GL (Fin 2) K :=
  ⟨blockS K, blockS K * blockS K, blockS_mul_blockS_mul, blockS_mul_mul_blockS⟩

theorem blockSGL_pow_three : blockSGL K ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  exact blockS_pow_three

@[expose] def blockPowGL (K : Type) [Field K] (k : ZMod 3) : GL (Fin 2) K :=
  blockSGL K ^ k.val

theorem blockPowGL_add (a b : ZMod 3) :
    blockPowGL K (a + b) = blockPowGL K a * blockPowGL K b := by
  unfold blockPowGL
  rw [← pow_add, ZMod.val_add]
  exact (pow_eq_pow_mod _ blockSGL_pow_three).symm

theorem blockPowGL_zero : blockPowGL K 0 = 1 := by
  simp [blockPowGL]

theorem blockPowGL_one : blockPowGL K 1 = blockSGL K := by
  simp [blockPowGL, show (1 : ZMod 3).val = 1 from rfl]

theorem det_blockPowGL (k : ZMod 3) :
    ((blockPowGL K k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  unfold blockPowGL
  rw [Units.val_pow_eq_pow_val, Matrix.det_pow]
  simp [blockSGL, det_blockS]

theorem blockPowGL_ne_one {k : ZMod 3} (hk : k ≠ 0) : blockPowGL K k ≠ 1 := by
  rcases zmod_three_eq_one_or_two hk with rfl | rfl
  · intro h
    apply blockS_ne_one (K := K)
    have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) h
    simpa [blockPowGL, blockSGL, show (1 : ZMod 3).val = 1 from rfl] using this
  · intro h
    apply blockS_mul_self_ne_one (K := K)
    have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) h
    simpa [blockPowGL, blockSGL, pow_two, show (2 : ZMod 3).val = 2 from rfl] using this

theorem blockPowGL_injective : Function.Injective (blockPowGL K) := by
  intro a b h
  have h1 : blockPowGL K (a - b) = 1 := by
    have : blockPowGL K a = blockPowGL K (a - b) * blockPowGL K b := by
      rw [← blockPowGL_add, sub_add_cancel]
    rw [h] at this
    exact (mul_eq_right.mp this.symm)
  by_contra hne
  exact blockPowGL_ne_one (sub_ne_zero.mpr hne) h1

theorem blockPowGL_mulVec_eq_self_of (k : ZMod 3) {x : Fin 2 → K} (hx : blockS K *ᵥ x = x) :
    ((blockPowGL K k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ x = x := by
  unfold blockPowGL
  rw [Units.val_pow_eq_pow_val]
  have key : ∀ m : ℕ,
      (((blockSGL K : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ m) *ᵥ x = x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec]
      have h1 : ((blockSGL K : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ x = x := hx
      rw [h1, ih]
  exact key _

theorem blockPowGL_mulVec_eq_self_iff {k : ZMod 3} (hk : k ≠ 0) (x : Fin 2 → K) :
    ((blockPowGL K k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ x = x ↔
      blockS K *ᵥ x = x := by
  refine ⟨fun h => ?_, blockPowGL_mulVec_eq_self_of k⟩
  rcases zmod_three_eq_one_or_two hk with rfl | rfl
  · simpa [blockPowGL, blockSGL, show (1 : ZMod 3).val = 1 from rfl] using h
  · have h2 : (blockS K * blockS K) *ᵥ x = x := by
      simpa [blockPowGL, blockSGL, pow_two, show (2 : ZMod 3).val = 2 from rfl] using h
    have h3 : blockS K *ᵥ ((blockS K * blockS K) *ᵥ x) = blockS K *ᵥ x := by rw [h2]
    rw [Matrix.mulVec_mulVec, blockS_mul_blockS_mul, Matrix.one_mulVec] at h3
    exact h3.symm

abbrev Blk : Type := Fin 2 × Fin 3

@[expose] def blkEquiv (hn : n = 6 ∨ n = 7) : Fin n ≃ Blk ⊕ Fin (n - 6) :=
  (finCongr (by omega : n = 6 + (n - 6))).trans
    (finSumFinEquiv.symm.trans
      (Equiv.sumCongr
        ((finProdFinEquiv : Fin 3 × Fin 2 ≃ Fin (3 * 2)).symm.trans
          (Equiv.prodComm (Fin 3) (Fin 2)))
        (Equiv.refl _)))

@[expose] def embMat (hn : n = 6 ∨ n = 7) (X : Matrix Blk Blk K) : Matrix (Fin n) (Fin n) K :=
  Matrix.reindex (blkEquiv hn).symm (blkEquiv hn).symm (Matrix.fromBlocks X 0 0 1)

theorem embMat_mul (hn : n = 6 ∨ n = 7) (X Y : Matrix Blk Blk K) :
    embMat hn (X * Y) = embMat hn X * embMat hn Y := by
  simp only [embMat, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]

theorem embMat_one (hn : n = 6 ∨ n = 7) : embMat hn (1 : Matrix Blk Blk K) = 1 := by
  simp [embMat, Matrix.fromBlocks_one]

theorem det_embMat (hn : n = 6 ∨ n = 7) (X : Matrix Blk Blk K) :
    (embMat hn X).det = X.det := by
  simp [embMat, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

theorem embMat_injective (hn : n = 6 ∨ n = 7) : Function.Injective (embMat (K := K) hn) := by
  intro X Y h
  have h1 := (Matrix.reindex (blkEquiv hn).symm (blkEquiv hn).symm).injective h
  exact (Matrix.fromBlocks_inj.mp h1).1

@[expose] def embMonoidHom (hn : n = 6 ∨ n = 7) :
    Matrix Blk Blk K →* Matrix (Fin n) (Fin n) K where
  toFun := embMat hn
  map_one' := embMat_one hn
  map_mul' := embMat_mul hn

@[expose] def embGL (hn : n = 6 ∨ n = 7) : GL Blk K →* GL (Fin n) K :=
  Units.map (embMonoidHom hn)

theorem coe_embGL (hn : n = 6 ∨ n = 7) (X : GL Blk K) :
    ((embGL hn X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      embMat hn (X : Matrix Blk Blk K) :=
  rfl

theorem embGL_injective (hn : n = 6 ∨ n = 7) : Function.Injective (embGL (K := K) hn) :=
  Units.map_injective (embMat_injective hn)

theorem embGL_mem_statedSL (hn : n = 6 ∨ n = 7) (X : GL Blk K)
    (hX : (X : Matrix Blk Blk K).det = 1) : embGL hn X ∈ StatedSL n K := by
  apply CFSG.Open.StatedAPI.mem_statedSL_of_det
  rw [coe_embGL, det_embMat, hX]

@[expose] def blockDiagGL (K : Type) [Field K] : (Fin 3 → GL (Fin 2) K) →* GL Blk K :=
  (Units.map (Matrix.blockDiagonalRingHom (Fin 2) (Fin 3) K).toMonoidHom).comp
    (MulEquiv.piUnits (M := fun _ : Fin 3 => Matrix (Fin 2) (Fin 2) K)).symm.toMonoidHom

theorem coe_blockDiagGL (M : Fin 3 → GL (Fin 2) K) :
    ((blockDiagGL K M : GL Blk K) : Matrix Blk Blk K) =
      Matrix.blockDiagonal fun i => ((M i : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem blockDiagGL_injective : Function.Injective (blockDiagGL K) := by
  intro M N h
  funext i
  apply Units.ext
  have h1 := congrArg (fun g : GL Blk K => (g : Matrix Blk Blk K)) h
  simp only [coe_blockDiagGL] at h1
  have h2 := Matrix.blockDiagonal_injective h1
  exact congrFun h2 i

@[expose] def blkGL (hn : n = 6 ∨ n = 7) : (Fin 3 → GL (Fin 2) K) →* GL (Fin n) K :=
  (embGL hn).comp (blockDiagGL K)

theorem coe_blkGL (hn : n = 6 ∨ n = 7) (M : Fin 3 → GL (Fin 2) K) :
    ((blkGL hn M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      embMat hn (Matrix.blockDiagonal fun i =>
        ((M i : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) :=
  rfl

theorem blkGL_injective (hn : n = 6 ∨ n = 7) : Function.Injective (blkGL (K := K) hn) :=
  (embGL_injective hn).comp blockDiagGL_injective

theorem det_blkGL (hn : n = 6 ∨ n = 7) (M : Fin 3 → GL (Fin 2) K) :
    ((blkGL hn M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det =
      ∏ i, ((M i : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det := by
  rw [coe_blkGL, det_embMat, Matrix.det_blockDiagonal]

theorem blkGL_mem_statedSL (hn : n = 6 ∨ n = 7) (M : Fin 3 → GL (Fin 2) K)
    (hM : ∏ i, ((M i : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1) :
    blkGL hn M ∈ StatedSL n K := by
  apply CFSG.Open.StatedAPI.mem_statedSL_of_det
  rw [det_blkGL, hM]

theorem blkGL_blockPowGL_mem (hn : n = 6 ∨ n = 7) (v : Fin 3 → ZMod 3) :
    blkGL hn (fun i => blockPowGL K (v i)) ∈ StatedSL n K :=
  blkGL_mem_statedSL hn _ (by simp [det_blockPowGL])

theorem blkGL_blockPowGL_add (hn : n = 6 ∨ n = 7) (v w : Fin 3 → ZMod 3) :
    blkGL hn (fun i => blockPowGL K (v i + w i)) =
      blkGL hn (fun i => blockPowGL K (v i)) * blkGL hn (fun i => blockPowGL K (w i)) := by
  rw [← map_mul]
  congr 1
  funext i
  exact blockPowGL_add _ _

theorem blkGL_blockPowGL_zero (hn : n = 6 ∨ n = 7) :
    blkGL hn (fun i => blockPowGL K ((0 : Fin 3 → ZMod 3) i)) = 1 := by
  have : (fun i => blockPowGL K ((0 : Fin 3 → ZMod 3) i)) = 1 := by
    funext i
    exact blockPowGL_zero
  rw [this, map_one]

@[expose] def c₀ (K : Type) [Field K] {n : ℕ} (hn : n = 6 ∨ n = 7) :
    Multiplicative (Fin 3 → ZMod 3) →* StatedSL n K where
  toFun v := ⟨blkGL hn fun i => blockPowGL K (Multiplicative.toAdd v i),
    blkGL_blockPowGL_mem hn _⟩
  map_one' := Subtype.ext (blkGL_blockPowGL_zero hn)
  map_mul' v w := Subtype.ext (blkGL_blockPowGL_add hn _ _)

theorem coe_c₀ (hn : n = 6 ∨ n = 7) (v : Multiplicative (Fin 3 → ZMod 3)) :
    ((c₀ K hn v : StatedSL n K) : GL (Fin n) K) =
      blkGL hn fun i => blockPowGL K (Multiplicative.toAdd v i) :=
  rfl

theorem c₀_injective (hn : n = 6 ∨ n = 7) : Function.Injective (c₀ K hn) := by
  intro v w h
  have h1 := congrArg (fun g : StatedSL n K => (g : GL (Fin n) K)) h
  simp only [coe_c₀] at h1
  have h2 := blkGL_injective hn h1
  apply Multiplicative.toAdd.injective
  funext i
  exact blockPowGL_injective (congrFun h2 i)

@[expose] def blkVec (hn : n = 6 ∨ n = 7) (w : Fin n → K) : Blk → K :=
  fun b => w ((blkEquiv hn).symm (Sum.inl b))

theorem embMat_mulVec_eq_self_iff (hn : n = 6 ∨ n = 7) (X : Matrix Blk Blk K) (w : Fin n → K) :
    embMat hn X *ᵥ w = w ↔ X *ᵥ blkVec hn w = blkVec hn w := by
  have key : embMat hn X *ᵥ w =
      ((Matrix.fromBlocks X 0 0 1) *ᵥ (w ∘ (blkEquiv hn).symm)) ∘ (blkEquiv hn) := by
    unfold embMat
    rw [Matrix.reindex_apply]
    simpa using Matrix.submatrix_mulVec_equiv (Matrix.fromBlocks X 0 0 1) w (blkEquiv hn)
      (blkEquiv hn)
  rw [key]
  set x : Blk ⊕ Fin (n - 6) → K := w ∘ (blkEquiv hn).symm with hx
  have hw : w = x ∘ (blkEquiv hn) := by
    funext a
    simp [hx]
  have hY : (Matrix.fromBlocks X 0 0 1 *ᵥ x = x) ↔ X *ᵥ (x ∘ Sum.inl) = x ∘ Sum.inl := by
    rw [Matrix.fromBlocks_mulVec]
    simp only [Matrix.zero_mulVec, add_zero, Matrix.one_mulVec, zero_add]
    constructor
    · intro h
      funext b
      exact congrFun h (Sum.inl b)
    · intro h
      funext b
      cases b with
      | inl b => exact congrFun h b
      | inr b => rfl
  have hblk : blkVec hn w = x ∘ Sum.inl := rfl
  rw [hblk, ← hY]
  constructor
  · intro h
    funext b
    have := congrFun h ((blkEquiv hn).symm b)
    simpa [hw] using this
  · intro h
    funext a
    rw [Function.comp_apply, h]
    simp [hw]

theorem blockDiagonal_mulVec_apply (M : Fin 3 → Matrix (Fin 2) (Fin 2) K) (x : Blk → K)
    (p : Fin 2) (i : Fin 3) :
    (Matrix.blockDiagonal M *ᵥ x) (p, i) = (M i *ᵥ fun q => x (q, i)) p := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.blockDiagonal_apply]
  rw [Finset.sum_comm]
  simp

theorem blockDiagonal_mulVec_eq_self_iff (M : Fin 3 → Matrix (Fin 2) (Fin 2) K) (x : Blk → K) :
    Matrix.blockDiagonal M *ᵥ x = x ↔
      ∀ i, M i *ᵥ (fun q => x (q, i)) = fun q => x (q, i) := by
  constructor
  · intro h i
    funext p
    have := congrFun h (p, i)
    rwa [blockDiagonal_mulVec_apply] at this
  · intro h
    funext ⟨p, i⟩
    rw [blockDiagonal_mulVec_apply]
    exact congrFun (h i) p

theorem c₀_mulVec_eq_self_iff (hn : n = 6 ∨ n = 7) (v : Multiplicative (Fin 3 → ZMod 3))
    (w : Fin n → K) :
    ((c₀ K hn v : StatedSL n K) : GL (Fin n) K).val.mulVec w = w ↔
      ∀ i : Fin 3, ((blockPowGL K (Multiplicative.toAdd v i) : GL (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) *ᵥ (fun q => blkVec hn w (q, i)) =
        fun q => blkVec hn w (q, i) := by
  change embMat hn (Matrix.blockDiagonal fun i =>
    ((blockPowGL K (Multiplicative.toAdd v i) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *ᵥ w =
      w ↔ _
  rw [embMat_mulVec_eq_self_iff, blockDiagonal_mulVec_eq_self_iff]

theorem fix_iff (hn : n = 6 ∨ n = 7) (v : Multiplicative (Fin 3 → ZMod 3)) :
    {w : Fin n → K | ((c₀ K hn v : StatedSL n K) : GL (Fin n) K).val.mulVec w = w} =
        {w : Fin n → K | ∀ v' : Multiplicative (Fin 3 → ZMod 3),
          ((c₀ K hn v' : StatedSL n K) : GL (Fin n) K).val.mulVec w = w} ↔
      ∀ i, Multiplicative.toAdd v i ≠ 0 := by
  constructor
  · intro h i hi
    set x : Blk → K := Pi.single (0, i) 1 with hx
    let w : Fin n → K := fun a => Sum.elim x 0 (blkEquiv hn a)
    have hwx : blkVec hn w = x := by
      funext b
      simp [blkVec, w]
    have hw1 : w ∈ {w : Fin n → K |
        ((c₀ K hn v : StatedSL n K) : GL (Fin n) K).val.mulVec w = w} := by
      rw [Set.mem_setOf_eq, c₀_mulVec_eq_self_iff, hwx]
      intro j
      by_cases hj : j = i
      · subst hj
        rw [hi, blockPowGL_zero]
        simp
      · have : (fun q => x (q, j)) = 0 := by
          funext q
          simp [hx, Pi.single_apply, hj]
        rw [this]
        simp
    rw [h] at hw1
    have h2 := hw1 (Multiplicative.ofAdd (Pi.single i 1))
    rw [c₀_mulVec_eq_self_iff, hwx] at h2
    have h3 := h2 i
    have h4 : (fun q => x (q, i)) = ![1, 0] := by
      funext q
      fin_cases q <;> simp [hx]
    rw [h4] at h3
    simp only [toAdd_ofAdd, Pi.single_eq_same] at h3
    rw [blockPowGL_one] at h3
    exact blockS_mulVec_ne_self h3
  · intro h
    ext w
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hw v'
      rw [c₀_mulVec_eq_self_iff] at hw ⊢
      intro i
      exact blockPowGL_mulVec_eq_self_of _
        ((blockPowGL_mulVec_eq_self_iff (h i) _).mp (hw i))
    · intro hw
      exact hw v

end CFSG.ClassicalGroups.SLnThreeLocal
