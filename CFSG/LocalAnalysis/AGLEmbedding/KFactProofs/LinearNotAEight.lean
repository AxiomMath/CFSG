module

import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.AGLEmbedding

namespace LinearNotAEight

open Matrix

theorem not_nonempty_equiv_alternatingGroup_eight_three_two :
    ¬ Nonempty (SpecialLinearGroup (Fin 3) (GaloisField 2 2) ⧸
        Subgroup.center (SpecialLinearGroup (Fin 3) (GaloisField 2 2)) ≃*
      alternatingGroup (Fin 8)) := by
  rintro ⟨e⟩
  have hX : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (SpecialLinearGroup (Fin 3) (GaloisField 2 2) ⧸
        Subgroup.center (SpecialLinearGroup (Fin 3) (GaloisField 2 2)))
      .PSL 3 2 2 := by
    refine ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩,
      GaloisField 2 2, inferInstance, inferInstance, ?_,
      ⟨CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 (GaloisField 2 2)⟩⟩
    rw [GaloisField.card 2 2 (by norm_num)]
  exact ((CFSG.ComponentClassification.PSL3Four.excludes_alternating_models_stated _ hX).2.2
    (Fin 8) (by simp)).false e

end LinearNotAEight

end CFSG.AGLEmbedding
