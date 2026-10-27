module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.PGSp45Identification

public section

namespace CFSG.EvenSporadicStandard.TwoHS.GH312

open CFSG.Open

theorem nonempty_mulEquiv_pgsp45_of_lieModel {X : Type} [Group X] [Finite X] (T : Subgroup X)
    [T.Normal] {p f : ℕ} (hq : p ^ f = 5) (hM : CFSG.Blueprint.LieModel T .PSp 2 p f)
    (hC : Subgroup.centralizer (T : Set X) = ⊥) (hT : T ≠ ⊤) : Nonempty (X ≃* PGSp45) :=
  nonempty_mulEquiv_pgsp45_of_statedClassicalModel T hq
    (hM.statedClassicalModel_of_ne_zero (by norm_num)) hC hT

end CFSG.EvenSporadicStandard.TwoHS.GH312
