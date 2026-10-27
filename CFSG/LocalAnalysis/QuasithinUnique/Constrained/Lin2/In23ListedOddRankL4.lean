module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNineLin

public section

namespace CFSG.QuasithinUnique.Lin2.OddRank

open CFSG.Assembly.LowTwoRank CFSG.SectionRank.ClassicalEven Matrix

theorem hasElemAb_nine_psl_four (K : Type) [Field K] :
    Id2519.HasElemAb 3 9 (StatedProj (StatedSL 4 K)) := by
  refine Id2519.hasElemAb_nine_statedProj (x := rotGL (0 : Fin 4) 1) (y := rotGL 2 3)
    (Subgroup.subset_closure (det_rotMatrix _ _)) (Subgroup.subset_closure (det_rotMatrix _ _))
    (rotGL_pow_three _ _) (rotGL_pow_three _ _)
    ⟨1, (StatedScalars _ K).one_mem, ?_⟩
    (fun hx => mul_scalar_ne (g := 1) (h := rotGL (0 : Fin 4) 1) (a := 0) (b := 1) (by decide)
      (one_mulVec _) (rotMatrix_mulVec_left _ _) hx (one_mul _))
    (fun n c hc => mul_scalar_ne (a := 2) (b := 3) (by decide)
      (rotGL_pow_mulVec_of_ne (by decide) (by decide) n) (rotMatrix_mulVec_left _ _) hc)
  rw [mul_one]
  exact (rotGL_commute (by decide) (by decide) (by decide) (by decide)).eq

end CFSG.QuasithinUnique.Lin2.OddRank
