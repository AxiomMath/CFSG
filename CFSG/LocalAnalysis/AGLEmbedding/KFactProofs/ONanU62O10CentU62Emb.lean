module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.U62ThreeCentGroup
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU62Model

public section

namespace CFSG.AGLEmbedding.U62O10Cent

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62
  CFSG.AGLEmbedding.U62ThreeCent

@[expose] noncomputable def blocksMat :
    Matrix (Fin 4) (Fin 4) F4 →* Matrix (Fin 4 ⊕ Fin 2) (Fin 4 ⊕ Fin 2) F4 where
  toFun A := fromBlocks A 0 0 1
  map_one' := fromBlocks_one
  map_mul' A B := by
    rw [fromBlocks_multiply]
    simp

@[expose] noncomputable def embMat (e : Fin 4 ⊕ Fin 2 ≃ Fin 6) :
    Matrix (Fin 4) (Fin 4) F4 →* Matrix (Fin 6) (Fin 6) F4 :=
  (Matrix.reindexAlgEquiv F4 F4 e).toAlgHom.toMonoidHom.comp blocksMat

theorem embMat_apply (e : Fin 4 ⊕ Fin 2 ≃ Fin 6) (A : Matrix (Fin 4) (Fin 4) F4)
    (p q : Fin 4 ⊕ Fin 2) : embMat e A (e p) (e q) = fromBlocks A 0 0 1 p q := by
  simp [embMat, blocksMat, Matrix.reindex_apply]

theorem embMat_transpose (e : Fin 4 ⊕ Fin 2 ≃ Fin 6) (A : Matrix (Fin 4) (Fin 4) F4) :
    (embMat e A)ᵀ = embMat e Aᵀ := by
  ext i j
  obtain ⟨p, rfl⟩ := e.surjective i
  obtain ⟨q, rfl⟩ := e.surjective j
  rw [Matrix.transpose_apply, embMat_apply, embMat_apply]
  rcases p with a | a <;> rcases q with b | b <;> simp [Matrix.one_apply, eq_comm]

theorem embMat_map (e : Fin 4 ⊕ Fin 2 ≃ Fin 6) (f : F4 →+* F4) (A : Matrix (Fin 4) (Fin 4) F4) :
    (embMat e A).map f = embMat e (A.map f) := by
  ext i j
  obtain ⟨p, rfl⟩ := e.surjective i
  obtain ⟨q, rfl⟩ := e.surjective j
  rw [Matrix.map_apply, embMat_apply, embMat_apply]
  rcases p with a | a <;> rcases q with b | b <;> simp [Matrix.one_apply]

theorem det_embMat (e : Fin 4 ⊕ Fin 2 ≃ Fin 6) (A : Matrix (Fin 4) (Fin 4) F4) :
    (embMat e A).det = A.det := by
  have : embMat e A = Matrix.reindex e e (fromBlocks A 0 0 1) := by
    simp [embMat, blocksMat]
  rw [this, det_reindex_self, det_fromBlocks_zero₂₁]
  simp

@[expose] noncomputable def embGL (e : Fin 4 ⊕ Fin 2 ≃ Fin 6) : GL (Fin 4) F4 →* GL (Fin 6) F4 :=
  Units.map (embMat e)

theorem coe_embGL (e : Fin 4 ⊕ Fin 2 ≃ Fin 6) (A : GL (Fin 4) F4) :
    ((embGL e A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      embMat e (A : Matrix (Fin 4) (Fin 4) F4) :=
  rfl

theorem embGL_mem_gramSU (e : Fin 4 ⊕ Fin 2 ≃ Fin 6) {A : GL (Fin 4) F4}
    (hA : A ∈ gramSU uData (1 : Matrix (Fin 4) (Fin 4) F4)) : embGL e A ∈ gramSU uData M6 := by
  obtain ⟨h1, h2⟩ := hA
  refine ⟨?_, ?_⟩
  · rw [coe_embGL, embMat_map, embMat_transpose, M6_eq_one, Matrix.mul_one, ← map_mul]
    rw [Matrix.mul_one] at h1
    rw [h1, map_one]
  · rw [coe_embGL, det_embMat, h2]

theorem embGL_commute (e : Fin 4 ⊕ Fin 2 ≃ Fin 6) (A : GL (Fin 4) F4) (d : Fin 6 → F4)
    (hd : ∀ a b : Fin 4, d (e (Sum.inl a)) = d (e (Sum.inl b))) :
    (embGL e A : Matrix (Fin 6) (Fin 6) F4) * Matrix.diagonal d =
      Matrix.diagonal d * (embGL e A : Matrix (Fin 6) (Fin 6) F4) := by
  ext i j
  obtain ⟨p, rfl⟩ := e.surjective i
  obtain ⟨q, rfl⟩ := e.surjective j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, coe_embGL, embMat_apply]
  rcases p with a | a <;> rcases q with b | b
  · simp [hd a b, mul_comm]
  · simp
  · simp
  · by_cases hab : a = b
    · subst hab
      simp [mul_comm]
    · simp [hab]

end CFSG.AGLEmbedding.U62O10Cent
