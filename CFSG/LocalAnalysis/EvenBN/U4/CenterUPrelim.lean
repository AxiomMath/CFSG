module

public import CFSG.LocalAnalysis.EvenBN.U4.RootF

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_sup mem_normalizer_inf)

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem IG_le_normalizer_F (hS : Setting h L η t Q T) :
    miyamotoIG h L η ≤ normalizer (miyamotoFG h L η t Q : Set G) := by
  intro x hx
  exact mem_normalizer_sup (hS.IG_le_normalizer_E hx)
    (mem_normalizer_inf (hS.IG_le_normalizer_F1 hx)
      (hS.IG_le_normalizer_centralizer hS.tori_le_IG.2.1 hx))

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
