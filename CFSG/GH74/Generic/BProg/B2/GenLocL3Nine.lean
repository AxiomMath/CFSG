module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3NineE2

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

theorem rank3_nine {K : Type} [Field K] [Finite K] (hK : Nat.card K = 9) :
    GenLocL3Nine.Rank3 K :=
  GenLocL3NineR3.rank3_of_exc hK (GenLocL3NineE3.excE3 hK) (GenLocL3NineE2.excE2 hK)

theorem genProp_psl3_nine {J : Type} [Group J] {p f : ℕ} (h9 : p ^ f = 9)
    (hJ : LieModel J .PSL 3 p f) : GenProp J :=
  genProp_psl3_nine_of_rank3 h9 (fun _ _ _ hF => rank3_nine hF) hJ

end CFSG.GH74.Generic.BProg.B2
