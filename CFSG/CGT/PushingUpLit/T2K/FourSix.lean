module

public import CFSG.CGT.PushingUpLit.T2K.Inputs

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Assembly

namespace T2Hyp

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}
variable (h : T2Hyp G L M n)
include h

theorem four_six (hE1 : FooteNonsolvableSimple) (hE5 : Aschbacher78One)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hnG4 : ¬ CFSG.GH74.SectionalTwoRankLE G 4) :
    Subgroup.normalizer (T : Set G) ≤ M :=
  (hE5 G L M n h (h.normal hE1) T hT).resolve_right hnG4

end T2Hyp

end CFSG.CGT.PushingUpLit.T2K
