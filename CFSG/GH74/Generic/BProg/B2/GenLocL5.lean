module

public import CFSG.GH74.Generic.BProg.B2.GenLocL5Out

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup

section L5

variable {A : Type} [Group A] [Finite A]

theorem not_sectional_l5_outer {J : Type} [Group J] [Finite J] (hJ : PuL5 J)
    (α : A →* MulAut J) (hA : IsRank23 A)
    (hout : ¬ α.range ≤ (MulAut.conj : J →* MulAut J).range) : ¬ SectionalTwoRankLE ↥(innJoin α) 4 :=
  GenLocL5Gen.not_sectional_of_out16 (GenLocL5Out.isSimpleGroup_of_puL5 hJ)
    (GenLocL5Out.out16_of_puL5 hJ) hA.1 α hout

theorem genLoc_l5 {J : Type} [Group J] [Finite J] (hJ : PuL5 J) : GenLoc4 J := by
  intro A _ _ α hA hsect
  left
  by_cases hin : α.range ≤ (MulAut.conj : J →* MulAut J).range
  · exact GenLocL5Out.genInner_of_puL5 hJ A α hA hin
  · exact absurd hsect (not_sectional_l5_outer hJ α hA hin)

end L5

end CFSG.GH74.Generic.BProg.B2
