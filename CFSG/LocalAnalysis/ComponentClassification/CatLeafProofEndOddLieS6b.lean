module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSkewNormal
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.EndOddSp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.Burgoyne.Sp

variable {K : Type} [Field K] (n : ℕ)

@[expose] def blkEquiv : Fin (2 + n) ⊕ Fin (2 + n) ≃ (Fin 2 ⊕ Fin 2) ⊕ (Fin n ⊕ Fin n) :=
  (Equiv.sumCongr finSumFinEquiv.symm finSumFinEquiv.symm).trans
    (Equiv.sumSumSumComm (Fin 2) (Fin n) (Fin 2) (Fin n))

theorem blkEquiv_inl_castAdd (i : Fin 2) :
    blkEquiv n (Sum.inl (Fin.castAdd n i)) = Sum.inl (Sum.inl i) := by
  simp [blkEquiv]

theorem blkEquiv_inl_natAdd (i : Fin n) :
    blkEquiv n (Sum.inl (Fin.natAdd 2 i)) = Sum.inr (Sum.inl i) := by
  simp [blkEquiv]

theorem blkEquiv_inr_castAdd (i : Fin 2) :
    blkEquiv n (Sum.inr (Fin.castAdd n i)) = Sum.inl (Sum.inr i) := by
  simp [blkEquiv]

theorem blkEquiv_inr_natAdd (i : Fin n) :
    blkEquiv n (Sum.inr (Fin.natAdd 2 i)) = Sum.inr (Sum.inr i) := by
  simp [blkEquiv]

variable {n}

@[expose] def blk (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    Matrix (Fin (2 + n) ⊕ Fin (2 + n)) (Fin (2 + n) ⊕ Fin (2 + n)) K :=
  (fromBlocks M 0 0 N).submatrix (blkEquiv n) (blkEquiv n)

theorem blk_mul (M M' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (N N' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    blk M N * blk M' N' = blk (M * M') (N * N') := by
  rw [blk, blk, blk, submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem blk_one : blk (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = 1 := by
  rw [blk, fromBlocks_one, submatrix_one_equiv]

theorem blk_transpose (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) : (blk M N)ᵀ = blk Mᵀ Nᵀ := by
  rw [blk, blk, transpose_submatrix, fromBlocks_transpose]
  simp

theorem fin_cases_add (i : Fin (2 + n)) :
    (∃ a : Fin 2, i = Fin.castAdd n a) ∨ ∃ b : Fin n, i = Fin.natAdd 2 b := by
  refine Fin.addCases (fun a => Or.inl ⟨a, rfl⟩) (fun b => Or.inr ⟨b, rfl⟩) i

theorem blk_apply_inl_inl (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (i j : Fin (2 + n)) :
    blk M N (Sum.inl i) (Sum.inl j) = fromBlocks M 0 0 N (blkEquiv n (Sum.inl i))
      (blkEquiv n (Sum.inl j)) := rfl

theorem formJ_eq_blk : formJ (2 + n) K = blk (formJ 2 K) (formJ n K) := by
  ext (i | i) (j | j) <;>
  rcases fin_cases_add i with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
  rcases fin_cases_add j with ⟨b, rfl⟩ | ⟨b, rfl⟩ <;>
  simp [blk, blkEquiv_inl_castAdd, blkEquiv_inl_natAdd, blkEquiv_inr_castAdd,
    blkEquiv_inr_natAdd, formJ, Matrix.one_apply, Fin.ext_iff, Fin.val_castAdd,
    Fin.val_natAdd] <;> omega

theorem skewNs_eq_blk (d : K) : skewNs (2 + n) K d = blk (skewNs 2 K d) (skewNs n K d) := by
  ext (i | i) (j | j) <;>
  rcases fin_cases_add i with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
  rcases fin_cases_add j with ⟨b, rfl⟩ | ⟨b, rfl⟩ <;>
  simp [blk, blkEquiv_inl_castAdd, blkEquiv_inl_natAdd, blkEquiv_inr_castAdd,
    blkEquiv_inr_natAdd, skewNs, Matrix.one_apply, Matrix.smul_apply, Fin.ext_iff,
    Fin.val_castAdd, Fin.val_natAdd] <;> omega

theorem blk_symplectic (g : StatedSp 2 K) :
    (blk ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) 1)ᵀ *
      formJ (2 + n) K * blk ((g : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) 1 = formJ (2 + n) K := by
  rw [formJ_eq_blk, blk_transpose, blk_mul, blk_mul, transpose_one, Matrix.one_mul,
    Matrix.mul_one, mem_statedSp_iff.1 g.2]

variable (n) in
@[expose] def spBlk : StatedSp 2 K →* StatedSp (2 + n) K where
  toFun g := ⟨⟨blk ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) 1,
      blk (((g : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) 1,
      by rw [blk_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one, blk_one],
      by rw [blk_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one, blk_one]⟩,
    mem_statedSp_iff.2 (blk_symplectic g)⟩
  map_one' := by
    apply statedSp_ext
    change blk _ 1 = 1
    rw [Subgroup.coe_one, Units.val_one, blk_one]
  map_mul' g h := by
    apply statedSp_ext
    change blk _ 1 = blk _ 1 * blk _ 1
    rw [blk_mul, Matrix.mul_one, Subgroup.coe_mul, Units.val_mul]

theorem coe_spBlk (g : StatedSp 2 K) :
    (((spBlk n g : StatedSp (2 + n) K) : GL (Fin (2 + n) ⊕ Fin (2 + n)) K) :
      Matrix (Fin (2 + n) ⊕ Fin (2 + n)) (Fin (2 + n) ⊕ Fin (2 + n)) K) =
      blk ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) 1 := rfl

theorem spBlk_commute {g : StatedSp 2 K} {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hg : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * M =
      M * ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
    (N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    (((spBlk n g : StatedSp (2 + n) K) : GL (Fin (2 + n) ⊕ Fin (2 + n)) K) :
      Matrix (Fin (2 + n) ⊕ Fin (2 + n)) (Fin (2 + n) ⊕ Fin (2 + n)) K) * blk M N =
      blk M N * (((spBlk n g : StatedSp (2 + n) K) : GL (Fin (2 + n) ⊕ Fin (2 + n)) K) :
        Matrix (Fin (2 + n) ⊕ Fin (2 + n)) (Fin (2 + n) ⊕ Fin (2 + n)) K) := by
  rw [coe_spBlk, blk_mul, blk_mul, hg, Matrix.one_mul, Matrix.mul_one]

theorem blk_neg_one_ne_smul (h2 : (2 : K) ≠ 0) (hn : 1 ≤ n) (c : K) :
    blk (-1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ≠ c • 1 := by
  intro h
  have e1 := congrFun (congrFun h (Sum.inl (Fin.castAdd n 0))) (Sum.inl (Fin.castAdd n 0))
  have e2 := congrFun (congrFun h (Sum.inl (Fin.natAdd 2 ⟨0, hn⟩)))
    (Sum.inl (Fin.natAdd 2 ⟨0, hn⟩))
  rw [blk_apply_inl_inl, blkEquiv_inl_castAdd] at e1
  rw [blk_apply_inl_inl, blkEquiv_inl_natAdd] at e2
  simp only [fromBlocks_apply₁₁, fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.one_apply_eq,
    Matrix.smul_apply, smul_eq_mul, mul_one] at e1 e2
  exact h2 (by linear_combination e2 - e1)

end CFSG.ComponentClassification.CatLeafProof.EndOddSp
