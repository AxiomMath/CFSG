module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912RowU6Core
public import CFSG.LocalAnalysis.GLTheoremA.PartI.SmallSUThreeCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

open CFSG CFSG.Open CFSG.Fischer Matrix
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.LocalAnalysis.GLTheoremA.SmallSUThreeCore
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

private noncomputable abbrev blockSU (d : Fin 6 → F4) (c : F4) : Subgroup (GL (Blk d c) F4) :=
  (StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4).comap
    (LevelLieU.reindexGL (Fintype.equivFin (Blk d c)))

private theorem blockSU_le_range_blkHom {d : Fin 6 → F4} {D : GL (Fin 6) F4}
    (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d) (c : F4) :
    blockSU d c ≤ (LevelLieU6.blkHom hD c).range := by
  intro A hA
  let B : ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4) :=
    ⟨LevelLieU.reindexGL (Fintype.equivFin (Blk d c)) A, hA⟩
  have hBcen : embSU d c B ∈ CenD D := embSU_mem_CenD d c hD B
  refine ⟨⟨embSU d c B, hBcen⟩, ?_⟩
  apply Units.ext
  rw [LevelLieU6.blkHom_val, mM6_embSU, blkM_extMat, LevelLieU.reindexGL_val]
  ext i j
  simp [Matrix.reindex_apply]

private theorem mem_blockSU_iff_det {d : Fin 6 → F4} {D : GL (Fin 6) F4}
    (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d) (c : F4)
    {y : GL (Blk d c) F4} (hy : y ∈ (LevelLieU6.blkHom hD c).range) :
    y ∈ blockSU d c ↔ (y : Matrix (Blk d c) (Blk d c) F4).det = 1 := by
  constructor
  · intro h
    exact det_eq_one_of_mem_comap_reindexGL (ι := Blk d c) h
  · intro hdet
    obtain ⟨z, rfl⟩ := hy
    have hd : (blkM d c (mM6 z.1)).det = 1 := by
      simpa [LevelLieU6.blkHom_val] using hdet
    rw [blockSU, Subgroup.mem_comap]
    apply LevelLieU.mem_statedSU_of
    · rw [LevelLieU.reindexGL_val, Matrix.det_reindex_self]
      exact hd
    · rw [LevelLieU.reindexGL_val]
      exact LevelLieU.reindex_unitary _ _ (blkM_unitary d c
        (fun i j hij => CenD_zero hD z hij) (M6_unitary z.1))

theorem u6TwoBlockCore_holds : U6TwoBlockCore := by
  intro d D hD c
  refine pPrimeCore_eq_bot_of_det_eq_one (blockSU_le_range_blkHom hD c)
    (fun y hy => mem_blockSU_iff_det hD c hy) ?_
  exact pPrimeCore_comap_reindexGL_statedSU_eq_bot (ι := Blk d c)
    (by simpa using Fintype.card_subtype_le (fun i : Fin 6 => d i = c))

end CFSG.LocalAnalysis.GLTheoremA.KD1912
