module

public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Foundations.Catalog

public section

namespace CFSG.SectionRank

theorem K_group_section_closure {X Y : Type} [Group X] [Group Y] (hX : IsKGroupCat X)
    (H : Subgroup X) (N : Subgroup H) [N.Normal] (f : H ⧸ N ≃* Y) : IsKGroupCat Y :=
  ((hX.subgroup H).quotient N).of_mulEquiv f.symm

theorem inCatalog_of_isKGroup_of_surjective {X : Type} [Group X] (hX : CFSG.IsKGroup X)
    (K : Subgroup X) {S : Type} [Group S] [IsSimpleGroup S] (φ : K →* S)
    (hφ : Function.Surjective φ) : CFSG.Assembly.InCatalog S :=
  hX.inCatalog_of_surjective K φ hφ

theorem K_group_section_closure_inCatalog {X Y : Type} [Group X] [Group Y]
    (hX : CFSG.IsKGroup X) (H : Subgroup X) (N : Subgroup H) [N.Normal] (f : H ⧸ N ≃* Y) :
    CFSG.IsKGroup Y :=
  ((hX.subgroup H).quotient N).of_mulEquiv f.symm

end CFSG.SectionRank
