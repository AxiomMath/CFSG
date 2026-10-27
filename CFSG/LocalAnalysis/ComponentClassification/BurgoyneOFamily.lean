module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOCore

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)

variable {K : Type} [Field K] {d a b : ℕ}

@[expose] def sumFin (hab : a + b = d) : Fin a ⊕ Fin b ≃ Fin d :=
  finSumFinEquiv.trans (finCongr hab)

theorem sumFin_inl (hab : a + b = d) (i : Fin a) : sumFin hab (.inl i) = ⟨i, by omega⟩ := by
  ext
  simp [sumFin]

theorem sumFin_inr (hab : a + b = d) (j : Fin b) :
    sumFin hab (.inr j) = ⟨a + j, by omega⟩ := by
  ext
  simp [sumFin]

@[expose] def famMat (hab : a + b = d) (c : Fin a ⊕ Fin b → Fin d → K) :
    Matrix (Fin d) (Fin d) K :=
  Matrix.of fun i l => c ((sumFin hab).symm l) i

@[expose] def famW (R : Matrix (Fin d) (Fin d) K) (hab : a + b = d)
    (c : Fin a ⊕ Fin b → Fin d → K) : Fin d → K :=
  fun l => c ((sumFin hab).symm l) ⬝ᵥ R *ᵥ c ((sumFin hab).symm l)

@[expose] def famJ (hab : a + b = d) : Finset (Fin d) :=
  Finset.univ.filter fun l => ((sumFin hab).symm l).isLeft

theorem famW_sumFin (R : Matrix (Fin d) (Fin d) K) (hab : a + b = d)
    (c : Fin a ⊕ Fin b → Fin d → K) (x : Fin a ⊕ Fin b) :
    famW R hab c (sumFin hab x) = c x ⬝ᵥ R *ᵥ c x := by
  simp only [famW, Equiv.symm_apply_apply]

theorem mem_famJ (hab : a + b = d) (l : Fin d) : l ∈ famJ hab ↔ (l : ℕ) < a := by
  obtain ⟨x, rfl⟩ := (sumFin hab).surjective l
  simp only [famJ, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
  rcases x with i | j
  · rw [sumFin_inl]
    simp [i.2]
  · rw [sumFin_inr]
    simp

theorem card_famJ (hab : a + b = d) : (famJ hab).card = a := by
  have : famJ hab = (Finset.univ : Finset (Fin a)).map
      (Function.Embedding.inl.trans (sumFin hab).toEmbedding) := by
    ext l
    obtain ⟨x, rfl⟩ := (sumFin hab).surjective l
    simp only [famJ, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply,
      Finset.mem_map, Function.Embedding.trans_apply, Function.Embedding.inl_apply,
      Equiv.coe_toEmbedding, EmbeddingLike.apply_eq_iff_eq]
    rcases x with i | j <;> simp
  rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem famMat_gram (R : Matrix (Fin d) (Fin d) K) (hab : a + b = d)
    (c : Fin a ⊕ Fin b → Fin d → K) (l l' : Fin d) :
    ((famMat hab c)ᵀ * R * famMat hab c) l l' =
      c ((sumFin hab).symm l) ⬝ᵥ R *ᵥ c ((sumFin hab).symm l') := by
  simp only [Matrix.mul_apply, transpose_apply, famMat, of_apply, dotProduct, mulVec,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem dotProduct_transpose_mul_mul (H M : Matrix (Fin d) (Fin d) K) (x : Fin d → K) :
    x ⬝ᵥ (Hᵀ * M * H) *ᵥ x = (H *ᵥ x) ⬝ᵥ M *ᵥ (H *ᵥ x) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

theorem exists_transport_of_family (h2 : (2 : K) ≠ 0) {R : GL (Fin d) K}
    {A : GL (Fin d) K} (hA : A ∈ matrixIsometries (oQ R)) (hab : a + b = d)
    (c : Fin a ⊕ Fin b → Fin d → K)
    (hcA : ∀ x, (A : Matrix (Fin d) (Fin d) K) *ᵥ c x = (if x.isLeft then (-1 : K) else 1) • c x)
    (horth : ∀ x y, x ≠ y → c x ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ c y = 0)
    (hdiag : ∀ x, c x ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ c x ≠ 0) :
    ∃ (hw : ∀ l, famW (R : Matrix (Fin d) (Fin d) K) hab c l ≠ 0) (S : GL (Fin d) K)
      (hS : ∀ v, oQ (diagGL hw) ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ((1 : Kˣ) : K) * oQ R v),
      transPair S 1 hS (linPair A hA) = sgnPair h2 hw (famJ hab) := by
  set H := famMat hab c with hH
  set w := famW (R : Matrix (Fin d) (Fin d) K) hab c with hwdef
  have hw : ∀ l, w l ≠ 0 := fun l => hdiag _
  have hgram : Hᵀ * (R : Matrix (Fin d) (Fin d) K) * H = diagonal w := by
    ext l l'
    rw [hH, famMat_gram, diagonal_apply]
    split_ifs with hll
    · rw [hll]
      rfl
    · exact horth _ _ fun e => hll ((sumFin hab).symm.injective e)
  have hdet : H.det ≠ 0 := by
    intro h0
    have e := congrArg Matrix.det hgram
    rw [det_mul, det_mul, det_transpose, h0, zero_mul, zero_mul, det_diagonal] at e
    exact (Finset.prod_ne_zero_iff.2 fun l _ => hw l) e.symm
  set Hg : GL (Fin d) K := Matrix.nonsingInvUnit H (isUnit_iff_ne_zero.2 hdet) with hHg
  have hHgv : ((Hg : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = H := rfl
  have hHHi : H * ((Hg⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [← hHgv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hS : ∀ v, oQ (diagGL hw) (((Hg⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v) =
      ((1 : Kˣ) : K) * oQ R v := by
    intro v
    rw [oQ_apply, oQ_apply, coe_diagGL, ← hgram, dotProduct_transpose_mul_mul, mulVec_mulVec,
      hHHi, one_mulVec, Units.val_one, one_mul]
  refine ⟨hw, Hg⁻¹, hS, ?_⟩
  have hAH : (A : Matrix (Fin d) (Fin d) K) * H = H * signMat K (famJ hab) := by
    ext i l
    rw [signMat, mul_diagonal]
    have e := congrFun (hcA ((sumFin hab).symm l)) i
    have e2 : ((A : Matrix (Fin d) (Fin d) K) * H) i l =
        ((A : Matrix (Fin d) (Fin d) K) *ᵥ c ((sumFin hab).symm l)) i := by
      rw [Matrix.mul_apply, mulVec, dotProduct]
      rfl
    rw [e2, e]
    simp only [Pi.smul_apply, smul_eq_mul, hH, famMat, of_apply, famJ, Finset.mem_filter,
      Finset.mem_univ, true_and]
    split_ifs <;> ring
  apply Subtype.ext
  apply SemidirectProduct.ext
  · rw [transPair_left, linPair_right, map_one, MulAut.one_apply]
    apply Units.ext
    change ((Hg⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (A : Matrix (Fin d) (Fin d) K) *
      (((Hg⁻¹)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = signMat K (famJ hab)
    rw [inv_inv, hHgv, Matrix.mul_assoc, hAH, ← Matrix.mul_assoc, ← hHgv, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mul]
  · rfl

end CFSG.ComponentClassification.Burgoyne.O
