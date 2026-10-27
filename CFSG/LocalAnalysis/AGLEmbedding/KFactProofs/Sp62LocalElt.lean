module

public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
public import CFSG.Quasithin.H13.L32NKGG22

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp62Local

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open CFSG.Quasithin.H13

theorem g22Form_eq_j6 : KGCert.g22Form =
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)).submatrix
      ε6 ε6 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem mat6_isIso (g : H6) :
    (mat6 g).transpose * KGCert.g22Form * mat6 g = KGCert.g22Form := by
  have h := (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff
    (g := (g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)))).1 g.2
  rw [g22Form_eq_j6, mat6_apply, Matrix.transpose_submatrix,
    Matrix.submatrix_mul_equiv _ _ _ ε6 _, Matrix.submatrix_mul_equiv _ _ _ ε6 _]
  exact congrArg (fun M => Matrix.submatrix M ε6 ε6) h

abbrev IsoMat (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Prop :=
  M.transpose * KGCert.g22Form * M = KGCert.g22Form

@[expose] def isoInv (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  KGCert.g22Form * M.transpose * KGCert.g22Form

theorem isoInv_mul {M : Matrix (Fin 6) (Fin 6) (ZMod 2)} (h : IsoMat M) : isoInv M * M = 1 := by
  rw [isoInv, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc M.transpose, h,
    KGCert.g22Form_mul_self]

theorem mul_isoInv {M : Matrix (Fin 6) (Fin 6) (ZMod 2)} (h : IsoMat M) : M * isoInv M = 1 :=
  mul_eq_one_comm.1 (isoInv_mul h)

theorem j6_eq_submatrix : (Matrix.fromBlocks 0 1 (-1) 0 :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) =
      KGCert.g22Form.submatrix ε6.symm ε6.symm := by
  rw [g22Form_eq_j6, Matrix.submatrix_submatrix, Equiv.self_comp_symm,
    Matrix.submatrix_id_id]

theorem submatrix_mem_statedSp {M : Matrix (Fin 6) (Fin 6) (ZMod 2)} (h : IsoMat M)
    (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) (hA : A = M.submatrix ε6.symm ε6.symm) :
    A.transpose * Matrix.fromBlocks 0 1 (-1) 0 * A = Matrix.fromBlocks 0 1 (-1) 0 := by
  subst hA
  rw [j6_eq_submatrix, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, h]

@[expose] def ofIso (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) (h : IsoMat M) : H6 :=
  ⟨⟨M.submatrix ε6.symm ε6.symm, (isoInv M).submatrix ε6.symm ε6.symm, by
      rw [Matrix.submatrix_mul_equiv, mul_isoInv h, Matrix.submatrix_one_equiv],
    by
      rw [Matrix.submatrix_mul_equiv, isoInv_mul h, Matrix.submatrix_one_equiv]⟩,
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff).2
      (submatrix_mem_statedSp h _ rfl)⟩

theorem mat6_ofIso (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) (h : IsoMat M) :
    mat6 (ofIso M h) = M := by
  rw [mat6_apply]
  show (M.submatrix ε6.symm ε6.symm).submatrix ε6 ε6 = M
  rw [Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]

end CFSG.AGLEmbedding.KFactProofs.Sp62Local
