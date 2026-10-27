module

public import CFSG.LieType.Simplicity.Classical
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.Open.StatedAPI

open CFSG.Assembly.LowTwoRank

theorem isSimpleGroup_of_statedClassicalModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (h : StatedClassicalModel X t n p f) : IsSimpleGroup X :=
  (LieType.Simplicity.fam_classical_converse X ⟨t, n, p, f, h⟩).2.2

end CFSG.Open.StatedAPI

namespace CFSG.Blueprint

open CFSG.Assembly.LowTwoRank

theorem LieModel.isSimpleGroup_of_mem_classicalTags {X : Type} [Group X] {t : StatedLieTag}
    {n p f : ℕ} (ht : t ∈ classicalTags) (h : LieModel X t n p f) : IsSimpleGroup X :=
  Open.StatedAPI.isSimpleGroup_of_statedClassicalModel (h.statedClassicalModel ht)

end CFSG.Blueprint
