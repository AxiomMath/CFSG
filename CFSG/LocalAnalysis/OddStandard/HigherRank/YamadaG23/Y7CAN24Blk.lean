module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4GL62Basic

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Matrix CFSG.OddStandard.AltStdSmall4.GL62

theorem n24_add_self {m n : Type*} (X : Matrix m n (ZMod 2)) : X + X = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  exact (by decide : ∀ x : ZMod 2, x + x = 0) _

@[expose] def n24Eq : Fin 3 ⊕ Fin 3 ≃ Fin 6 := finSumFinEquiv

@[simp] theorem n24Eq_symm_castAdd (i : Fin 3) : n24Eq.symm (Fin.castAdd 3 i) = Sum.inl i :=
  finSumFinEquiv_symm_apply_castAdd i

@[simp] theorem n24Eq_symm_natAdd (i : Fin 3) : n24Eq.symm (Fin.natAdd 3 i) = Sum.inr i :=
  finSumFinEquiv_symm_apply_natAdd i

@[simp] theorem n24Eq_symm_addNat (i : Fin 3) : n24Eq.symm (i.addNat 3) = Sum.inr i := by
  rw [← Fin.natAdd_eq_addNat]
  exact finSumFinEquiv_symm_apply_natAdd i

@[expose] def n24Blk (P Q R S : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  (Matrix.fromBlocks P Q R S).submatrix n24Eq.symm n24Eq.symm

theorem n24Blk_ll (P Q R S : Matrix (Fin 3) (Fin 3) (ZMod 2)) (i j : Fin 3) :
    n24Blk P Q R S (Fin.castAdd 3 i) (Fin.castAdd 3 j) = P i j := by
  simp [n24Blk]

theorem n24Blk_lr (P Q R S : Matrix (Fin 3) (Fin 3) (ZMod 2)) (i j : Fin 3) :
    n24Blk P Q R S (Fin.castAdd 3 i) (Fin.natAdd 3 j) = Q i j := by
  simp [n24Blk]

theorem n24Blk_rl (P Q R S : Matrix (Fin 3) (Fin 3) (ZMod 2)) (i j : Fin 3) :
    n24Blk P Q R S (Fin.natAdd 3 i) (Fin.castAdd 3 j) = R i j := by
  simp [n24Blk]

theorem n24Blk_rr (P Q R S : Matrix (Fin 3) (Fin 3) (ZMod 2)) (i j : Fin 3) :
    n24Blk P Q R S (Fin.natAdd 3 i) (Fin.natAdd 3 j) = S i j := by
  simp [n24Blk]

theorem n24Blk_mul (P Q R S P' Q' R' S' : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    n24Blk P Q R S * n24Blk P' Q' R' S' =
      n24Blk (P * P' + Q * R') (P * Q' + Q * S') (R * P' + S * R') (R * Q' + S * S') := by
  unfold n24Blk
  rw [Matrix.submatrix_mul_equiv _ _ n24Eq.symm n24Eq.symm n24Eq.symm,
    Matrix.fromBlocks_multiply]

theorem n24Blk_one : n24Blk 1 0 0 1 = 1 := by
  unfold n24Blk
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem n24Blk_inj {P Q R S P' Q' R' S' : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (h : n24Blk P Q R S = n24Blk P' Q' R' S') : P = P' ∧ Q = Q' ∧ R = R' ∧ S = S' := by
  have h' : Matrix.fromBlocks P Q R S = Matrix.fromBlocks P' Q' R' S' := by
    have := congrArg (fun M => M.submatrix n24Eq n24Eq) h
    simpa [n24Blk, Matrix.submatrix_submatrix] using this
  exact Matrix.fromBlocks_inj.mp h'

theorem exists_n24Blk (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    ∃ P Q R S : Matrix (Fin 3) (Fin 3) (ZMod 2), M = n24Blk P Q R S := by
  refine ⟨M.submatrix (Fin.castAdd 3) (Fin.castAdd 3), M.submatrix (Fin.castAdd 3) (Fin.natAdd 3),
    M.submatrix (Fin.natAdd 3) (Fin.castAdd 3), M.submatrix (Fin.natAdd 3) (Fin.natAdd 3), ?_⟩
  ext i j
  refine Fin.addCases (m := 3) (n := 3) (fun a => ?_) (fun a => ?_) i <;>
    refine Fin.addCases (m := 3) (n := 3) (fun b => ?_) (fun b => ?_) j
  · rw [n24Blk_ll]; rfl
  · rw [n24Blk_lr]; rfl
  · rw [n24Blk_rl]; rfl
  · rw [n24Blk_rr]; rfl

theorem z0_eq_blk : (z₀ : Matrix (Fin 6) (Fin 6) (ZMod 2)) = n24Blk 1 1 0 1 := by
  decide

theorem dg_eq_blk (A : GL (Fin 3) (ZMod 2)) :
    (dg A : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      n24Blk (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0 (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  rw [coe_dg]
  ext i j
  refine Fin.addCases (m := 3) (n := 3) (fun a => ?_) (fun a => ?_) i <;>
    refine Fin.addCases (m := 3) (n := 3) (fun b => ?_) (fun b => ?_) j
  · rw [dgMat_ll, n24Blk_ll]
  · rw [dgMat_lr, n24Blk_lr]; rfl
  · rw [dgMat_rl, n24Blk_rl]; rfl
  · rw [dgMat_rr, n24Blk_rr]

end CFSG.OddStandard.HigherRank.YamadaG23
