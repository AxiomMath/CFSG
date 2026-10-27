module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245BaumannDouble

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin Subgroup

namespace C56

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem baumann_cs (hcs : ConstrainedSetting G T M H S L) (hj : conjJoin S L = L)
    (hL : (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 3) :
    baum S ≤ normalizer (L : Set G) ∧ IsSylowTwoOf (baum S) (L ⊔ baum S) :=
  baumann_single hcs.minParabolic hcs.block hL hcs.thompson (H_eq hcs hj) (S_le_normalizer hj)

theorem baumann_A3_cs (hcs : ConstrainedSetting G T M H S L) (h3 : IsAltType L 3) :
    blockU L ≤ baum S ∧ baum S ≤ normalizer (L : Set G) ∧
      IsSylowTwoOf (baum S) (L ⊔ baum S) := by
  by_cases hj : conjJoin S L = L
  · exact baumann_A3_single hcs.minParabolic hcs.block h3 hcs.thompson (H_eq hcs hj)
      (S_le_normalizer hj)
  · exact baumann_double_A3 hcs h3 hj

end C56

end CFSG.QuasithinUnique
