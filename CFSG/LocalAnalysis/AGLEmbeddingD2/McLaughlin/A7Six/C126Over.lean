module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenSolvC126

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Six

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN

variable {G : Type} [Group G] [Finite G]

theorem concl1_over {C₁ C₂ H S T M : Subgroup G} (hP : IsC118Pair T C₁ C₂)
    (hB : baum S = baum T) (h1S : C₁ ≤ omegaOneCenterOf S)
    (hmin : MinParabolic H S M) (hF : CharTwo H)
    (hsolv : perfectCore H ≤ Subgroup.centralizer (VZ S H : Set G)) : Concl1Gen C₁ C₂ H S :=
  concl1Gen_of_perfectCore_le_weak (hP.toWeakOfBaumEq hB h1S) hmin hF hsolv

end CFSG.AGLEmbeddingD2.McLaughlin.A7Six
