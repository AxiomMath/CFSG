module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerSingerAffine
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.ParabolicCover

public section

noncomputable section

namespace CFSG.AGLEmbeddingD2.McLaughlin.Lie

open TauCeti CFSG.Assembly.LowTwoRank CFSG.ClassicalModels
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem isLThreeTwo_of_statedClassicalModel {G : Type} [Group G]
    (h : StatedClassicalModel G .PSL 2 7 1) : IsLThreeTwo G := by
  let q : PrimePower := ⟨7, 1, h.1.1, by norm_num⟩
  have : Fact (Nat.Prime 7) := ⟨h.1.1⟩
  have hdup : ¬ LieTypeIndex.IsDuplicateRepresentative
      (LieTypeIndex.A (2 - 1) ⟨7, 1, h.1.1, by have hf := h.1.2.1; omega⟩) := by
    rw [LieTypeIndex.isDuplicateRepresentative_iff]
    simp only [PrimePower.card_def]
    omega
  have hv := linearCatalog_index_valid 2 7 1 h.1 hdup
  obtain ⟨K, hfield, hfinite, hKcard, ⟨e⟩⟩ := h.2
  let _ := hfield
  let _ := hfinite
  let eK := statedLinearModelEquivGaloisPSL K 2 7 1 (by norm_num) hKcard
  let eC := linearCatalogCandidateEquivPSL (2 - 1) q hv
  have hq : q.card = 7 := by rw [PrimePower.card_def]; norm_num [q]
  exact ⟨⟨LieTypeIndex.A 1 q, hv⟩, ⟨q, hq, rfl⟩, ⟨(e.trans eK).trans eC.symm⟩⟩

theorem isLThreeTwo_GL_three_two : IsLThreeTwo (GL (Fin 3) (ZMod 2)) := by
  have := CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger.isSimpleGroup_GL_three_zmod_two
  obtain ⟨-, -, -, -, -, -, -, hmodel⟩ :=
    CFSG.ProperTwoGeneratedCore.CosetNormalizer.simple_order_168_without_six_projective_seven_recognition
      (GL (Fin 3) (ZMod 2))
      (CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger.exists_mul_ne_mul_GL_three_zmod_two)
      CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger.card_GL_three_zmod_two
      CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger.orderOf_ne_six_GL_three_zmod_two
  exact isLThreeTwo_of_statedClassicalModel hmodel

end CFSG.AGLEmbeddingD2.McLaughlin.Lie
