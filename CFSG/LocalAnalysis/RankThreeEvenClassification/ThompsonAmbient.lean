module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThompsonFoundations
import CFSG.LocalAnalysis.RankThreeEvenClassification.ThompsonCanonical
import CFSG.Foundations.MaxOrderThompson

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

@[expose, reducible] noncomputable def thompsonCenterOf {G : Type u} [Group G] (subgroup : Subgroup G) :
    Subgroup G :=
  CFSG.ambientOrderZJ subgroup

theorem thompsonOrderCenter_commutative (G : Type u) [Group G] :
    IsMulCommutative (thompsonOrderCenter G) := by
  rw [thompsonOrderCenter_eq_orderZJ]
  infer_instance

theorem thompsonOrderCenter_normal (G : Type u) [Group G] [Finite G] :
    (thompsonOrderCenter G).Normal := by
  rw [thompsonOrderCenter_eq_orderZJ]
  infer_instance

theorem thompsonCenterOf_le {G : Type u} [Group G] (subgroup : Subgroup G) :
    thompsonCenterOf subgroup ≤ subgroup := Subgroup.map_subtype_le _

theorem thompsonCenterOf_commutative {G : Type u} [Group G] (subgroup : Subgroup G) :
    IsMulCommutative (thompsonCenterOf subgroup) :=
  CFSG.ambientOrderZJ_isMulCommutative subgroup

theorem thompsonCenterOf_normalized {G : Type u} [Group G] [Finite G] (subgroup : Subgroup G) :
    Subgroup.normalizer (subgroup : Set G) ≤ Subgroup.normalizer (thompsonCenterOf subgroup : Set G) :=
  CFSG.normalizer_le_normalizer_ambientOrderZJ subgroup

end CFSG.RankThreeEvenClassification.Helpers
