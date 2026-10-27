module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThompsonFoundations
import CFSG.LocalAnalysis.RankThreeEvenClassification.ThompsonCanonical
import CFSG.Foundations.MaxOrderThompson

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem maximumAbelianOrder_equiv {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (equivalence : G ≃* H) : maximumAbelianOrder G = maximumAbelianOrder H :=
  CFSG.maxAbelianOrder_eq_of_mulEquiv equivalence

theorem MaximumOrderAbelian.map_equiv {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (equivalence : G ≃* H) (subgroup : Subgroup G) (hmaximum : MaximumOrderAbelian subgroup) :
    MaximumOrderAbelian (subgroup.map equivalence.toMonoidHom) :=
  CFSG.map_mem_maxOrderAbelianFamily equivalence hmaximum

theorem thompsonOrderSubgroup_map_equiv {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (equivalence : G ≃* H) : (thompsonOrderSubgroup G).map equivalence.toMonoidHom = thompsonOrderSubgroup H := by
  rw [thompsonOrderSubgroup_eq_orderThompson, thompsonOrderSubgroup_eq_orderThompson]
  exact CFSG.map_orderThompson equivalence

theorem thompsonOrderCenter_map_equiv {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (equivalence : G ≃* H) : (thompsonOrderCenter G).map equivalence.toMonoidHom = thompsonOrderCenter H := by
  rw [thompsonOrderCenter_eq_orderZJ, thompsonOrderCenter_eq_orderZJ]
  exact CFSG.map_orderZJ equivalence

theorem thompsonOrderSubgroup_characteristic (G : Type u) [Group G] [Finite G] :
    (thompsonOrderSubgroup G).Characteristic := by
  rw [thompsonOrderSubgroup_eq_orderThompson]
  infer_instance

theorem thompsonOrderCenter_characteristic (G : Type u) [Group G] [Finite G] :
    (thompsonOrderCenter G).Characteristic := by
  rw [thompsonOrderCenter_eq_orderZJ]
  infer_instance

theorem maximumAbelianOrder_subgroup_eq_of_contains_maximum {G : Type u} [Group G] [Finite G]
    (subgroup maximum : Subgroup G) (hmaximum : MaximumOrderAbelian maximum) (hle : maximum ≤ subgroup) :
    maximumAbelianOrder subgroup = maximumAbelianOrder G :=
  CFSG.maxAbelianOrder_subgroup_eq hmaximum hle

theorem thompsonOrderCenter_le_of_contains_maximum {G : Type u} [Group G] [Finite G]
    (subgroup maximum : Subgroup G) (hmaximum : MaximumOrderAbelian maximum) (hle : maximum ≤ subgroup) :
    thompsonOrderCenter G ≤ (thompsonOrderCenter subgroup).map subgroup.subtype := by
  rw [thompsonOrderCenter_eq_orderZJ, thompsonOrderCenter_eq_orderZJ]
  exact CFSG.orderZJ_le_ambientOrderZJ hmaximum hle

end CFSG.RankThreeEvenClassification.Helpers
