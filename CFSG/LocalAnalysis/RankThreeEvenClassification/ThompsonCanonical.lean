module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThompsonFoundations

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem maximumAbelianOrder_eq_maxAbelianOrder (G : Type u) [Group G] :
    maximumAbelianOrder G = CFSG.maxAbelianOrder G :=
  rfl

theorem maximumOrderAbelian_iff_mem_maxOrderAbelianFamily {G : Type u} [Group G] (A : Subgroup G) :
    MaximumOrderAbelian A ↔ A ∈ CFSG.maxOrderAbelianFamily G :=
  Iff.rfl

theorem thompsonOrderSubgroup_eq_orderThompson (G : Type u) [Group G] :
    thompsonOrderSubgroup G = CFSG.orderThompson G :=
  rfl

theorem thompsonOrderCenter_eq_orderZJ (G : Type u) [Group G] :
    thompsonOrderCenter G = CFSG.orderZJ G :=
  rfl

end CFSG.RankThreeEvenClassification.Helpers
