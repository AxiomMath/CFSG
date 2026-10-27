module

public import CFSG.ClassicalInvolution.RankTwo.Reduction
import CFSG.Assembly.LowTwoRank
import CFSG.LocalAnalysis.RankTwoShapes.IsomorphismTypesFromTheoremBStar
import CFSG.CharacterTheory.Semidihedral.AllPrimeQDInputs

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open

theorem oddLieType_or_m11_of_twoRank_le_two (F : Type) [Group F] [Finite F] [IsSimpleGroup F]
    (hnab : ∃ a b : F, a * b ≠ b * a) (h2 : CFSG.Assembly.twoRank F ≤ 2)
    (z : F) (hz : orderOf z = 2) (K : Subgroup F) (_hzK : z ∈ K)
    (_hK : IsSubnormal K (Subgroup.centralizer ({z} : Set F))) (hw : classicalInvolutionWitness K)
    (_hns : ¬ Group.IsSolvable K) :
    Blueprint.OddLieType F ∨ Blueprint.NativeSporadic.IsSporadic F .M11 := by
  have heven : Even (Nat.card F) := even_iff_two_dvd.mpr (hz ▸ orderOf_dvd_natCard z)
  have h2' : CFSG.Assembly.twoRank F = 2 :=
    le_antisymm h2 (CFSG.Assembly.LowTwoRank.two_le_twoRank F hnab heven)
  exact oddLieType_or_m11_of_rankTwoTypes hnab hw
    (CFSG.RankTwoShapes.rank_two_isomorphism_types_of_semidihedral_theoremBStar
      CFSG.Semidihedral.AllPrime.stationaryCoverageStatement F hnab h2')

end CFSG.ClassicalInvolution
