module

public import Mathlib.LinearAlgebra.Matrix.Reindex

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

open Matrix

variable {K : Type} [Field K]

@[expose] def e6 : Fin 4 ⊕ Fin 2 ≃ Fin 6 := finSumFinEquiv

@[expose] def ia (a : Fin 4) : Fin 6 := ⟨a.val, by omega⟩

@[expose] def ib (b : Fin 2) : Fin 6 := ⟨4 + b.val, by omega⟩

@[expose] def blk6 (M : Matrix (Fin 4) (Fin 4) K) (N : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 6) (Fin 6) K :=
  Matrix.reindexAlgEquiv K K e6 (Matrix.fromBlocks M 0 0 N)

theorem blk6_mul (M M' : Matrix (Fin 4) (Fin 4) K) (N N' : Matrix (Fin 2) (Fin 2) K) :
    blk6 (M * M') (N * N') = blk6 M N * blk6 M' N' := by
  unfold blk6
  rw [← map_mul, Matrix.fromBlocks_multiply]
  simp

theorem blk6_one : blk6 (1 : Matrix (Fin 4) (Fin 4) K) (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  unfold blk6
  rw [Matrix.fromBlocks_one, map_one]

theorem e6_symm_ia (a : Fin 4) : e6.symm (ia a) = Sum.inl a := by
  unfold e6 ia
  rw [Equiv.symm_apply_eq]
  rfl

theorem e6_symm_ib (b : Fin 2) : e6.symm (ib b) = Sum.inr b := by
  unfold e6 ib
  rw [Equiv.symm_apply_eq]
  rfl

theorem blk6_ia_ia (M : Matrix (Fin 4) (Fin 4) K) (N : Matrix (Fin 2) (Fin 2) K) (a b : Fin 4) :
    blk6 M N (ia a) (ia b) = M a b := by
  simp [blk6, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, e6_symm_ia]

theorem blk6_ib_ib (M : Matrix (Fin 4) (Fin 4) K) (N : Matrix (Fin 2) (Fin 2) K) (a b : Fin 2) :
    blk6 M N (ib a) (ib b) = N a b := by
  simp [blk6, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, e6_symm_ib]

theorem blk6_ia_ib (M : Matrix (Fin 4) (Fin 4) K) (N : Matrix (Fin 2) (Fin 2) K) (a : Fin 4)
    (b : Fin 2) : blk6 M N (ia a) (ib b) = 0 := by
  simp [blk6, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, e6_symm_ia, e6_symm_ib]

theorem blk6_ib_ia (M : Matrix (Fin 4) (Fin 4) K) (N : Matrix (Fin 2) (Fin 2) K) (a : Fin 2)
    (b : Fin 4) : blk6 M N (ib a) (ia b) = 0 := by
  simp [blk6, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, e6_symm_ia, e6_symm_ib]

theorem eq_blk6_of_offblock (M : Matrix (Fin 6) (Fin 6) K)
    (h1 : ∀ a b, M (ia a) (ib b) = 0) (h2 : ∀ a b, M (ib a) (ia b) = 0) :
    M = blk6 (Matrix.of fun a b => M (ia a) (ia b)) (Matrix.of fun a b => M (ib a) (ib b)) := by
  ext i j
  obtain ⟨x, rfl⟩ := e6.surjective i
  obtain ⟨y, rfl⟩ := e6.surjective j
  rcases x with a | a <;> rcases y with b | b
  · rw [show e6 (Sum.inl a) = ia a from rfl, show e6 (Sum.inl b) = ia b from rfl, blk6_ia_ia]
    simp
  · rw [show e6 (Sum.inl a) = ia a from rfl, show e6 (Sum.inr b) = ib b from rfl, blk6_ia_ib,
      h1]
  · rw [show e6 (Sum.inr a) = ib a from rfl, show e6 (Sum.inl b) = ia b from rfl, blk6_ib_ia,
      h2]
  · rw [show e6 (Sum.inr a) = ib a from rfl, show e6 (Sum.inr b) = ib b from rfl, blk6_ib_ib]
    simp

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

end
