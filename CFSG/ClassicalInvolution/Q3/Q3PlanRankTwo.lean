module

public import CFSG.ClassicalInvolution.Q3.Tight
public import CFSG.ClassicalInvolution.RankTwo.Reduction
public import CFSG.Assembly.LowTwoRank
public import CFSG.LocalAnalysis.RankTwoShapes.IsomorphismTypesFromTheoremBStar
public import CFSG.CharacterTheory.Semidihedral.AllPrimeQDInputs

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open

theorem citRankTwo3 :
    ∀ (F : Type) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
      ∀ (z : F) (K : Subgroup F), IsClassicalMember3 K z → twoRank F ≤ 2 →
        Blueprint.OddLieType F ∨ Blueprint.NativeSporadic.IsSporadic F .M11 := by
  intro F _ _ _ hnab z K hK h2
  have heven : Even (Nat.card F) :=
    even_iff_two_dvd.mpr (hK.orderOf_eq_two ▸ orderOf_dvd_natCard z)
  have h2' : CFSG.Assembly.twoRank F = 2 :=
    le_antisymm h2 (CFSG.Assembly.LowTwoRank.two_le_twoRank F hnab heven)
  exact oddLieType_or_m11_of_rankTwoTypes hnab hK.witness
    (CFSG.RankTwoShapes.rank_two_isomorphism_types_of_semidihedral_theoremBStar
      CFSG.Semidihedral.AllPrime.stationaryCoverageStatement F hnab h2')

end CFSG.ClassicalInvolution.Q3
