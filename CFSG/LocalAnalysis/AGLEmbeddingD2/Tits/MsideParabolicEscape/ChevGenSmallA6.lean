module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenLatCert

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

open Equiv CFSG.QuasithinUnique.L246C127 CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

theorem even6_closure_le (L : List (Perm (Fin 6))) (h : ∀ g ∈ L, Perm.sign g = 1) :
    Subgroup.closure {g | g ∈ L} ≤ alternatingGroup (Fin 6) := by
  rw [Subgroup.closure_le]
  exact fun g hg => Equiv.Perm.mem_alternatingGroup.2 (h g hg)

theorem yData_alt_six :
    YData ↥(alternatingGroup (Fin 6)) (Even6.D.subgroupOf (alternatingGroup (Fin 6))) := by
  refine yData_of_latCert Even6.cert Even6.closure_mGens Even6.D_le Even6.cert_check
    Even6.L1 Even6.L2 Even6.L3 rfl 8 24 360 rfl rfl 3 (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (even6_closure_le _ (by decide +kernel)) (even6_closure_le _ (by decide +kernel))
    3 (by decide +kernel) (by decide +kernel)
    ⟨![0, 0, 0, 0, 1, 1], by decide +kernel,
      permOf 6 [[2, 4], [3, 5]], by decide +kernel, 2, by decide +kernel⟩ ?_ ?_
  · refine ⟨evalW Even6.L1 [1, 2], evalW_mem_closure _ _, evalW Even6.L1 [1],
      evalW_mem_closure _ _, ?_, by decide +kernel⟩
    refine orderOf_eq_prime ?_ (by decide +kernel)
    show evalW Even6.L1 [1, 2] ^ 3 = 1
    decide +kernel
  · refine ⟨evalW Even6.L2 [0, 2], evalW_mem_closure _ _, evalW Even6.L2 [0],
      evalW_mem_closure _ _, ?_, by decide +kernel⟩
    refine orderOf_eq_prime ?_ (by decide +kernel)
    show evalW Even6.L2 [0, 2] ^ 3 = 1
    decide +kernel

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen
