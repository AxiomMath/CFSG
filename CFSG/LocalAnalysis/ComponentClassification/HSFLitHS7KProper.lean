module

public import CFSG.LocalAnalysis.ComponentInitial.KProperSubgroup
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.ComponentClassification.HSFLit.HS7

open CFSG Subgroup

theorem kProper_quotient {C : Assembly.GroupProp}
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X) {Y : Type} [Group Y]
    (hK : Assembly.KProper C Y) (M : Subgroup Y) [M.Normal] : Assembly.KProper C (Y ⧸ M) :=
  CFSG.KCore.KProperNonab.quotient hC hK M

theorem kProper_quotient_catalog {Y : Type} [Group Y]
    (hK : Assembly.KProper Blueprint.Catalog Y) (M : Subgroup Y) [M.Normal] :
    Assembly.KProper Blueprint.Catalog (Y ⧸ M) :=
  kProper_quotient (fun e h => (SectionRank.catalog_congr e).mpr h) hK M

theorem kProper_subgroup_catalog {Y : Type} [Group Y]
    (hK : Assembly.KProper Blueprint.Catalog Y) (H : Subgroup Y) :
    Assembly.KProper Blueprint.Catalog H :=
  LocalAnalysis.ComponentInitial.kProper_subgroup (fun e h => (SectionRank.catalog_congr e).mpr h)
    hK H

end CFSG.ComponentClassification.HSFLit.HS7
