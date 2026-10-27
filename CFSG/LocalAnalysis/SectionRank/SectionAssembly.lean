
module

public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase1

public import CFSG.Sporadic.J4

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.Blueprint

theorem j4OrderHyp : J4OrderHyp := by
  unfold J4OrderHyp
  rw [CFSG.Sporadic.J4.card_J4]

theorem catalogStepHyp
    : CatalogStepHyp := catalogStepHyp_of_J4 j4OrderHyp

theorem sqt_catalog_of_simple_section_of_sqtk
    {X : Type} [Group X] [Finite X] (hX : IsSQTKCat X)
    (H : Subgroup X) (N : Subgroup H) [N.Normal] [IsSimpleGroup (H ⧸ N)]
    (hnonab : ∃ a b : H ⧸ N, a * b ≠ b * a) :
    IsStronglyQuasithin (H ⧸ N) ∧ Catalog (H ⧸ N) :=
  sqt_catalog_of_simple_section_of_J4 j4OrderHyp hX H N hnonab

end CFSG.SectionRank
