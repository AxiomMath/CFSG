module

public import CFSG.GH74.Generic.BProg.B2.GenLocU3E8Frame

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.GH74 CFSG.Blueprint CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.GH74.Generic.BProg.B2.GenLocU3Lift CFSG.GH74.KGroups.L3Eps.Uni
  CFSG.GH74.Generic.BProg.B2.GenLocU3Blk CFSG.LieType.Steinberg
  CFSG.GH74.Generic.BProg.B2.GenLocU3NF CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
open scoped MatrixGroups

theorem exc7E8Hyp {J : Type} [Group J] {p f : ℕ} (hq : p ^ f = 7) :
    GenLocU3Seven.Exc7E8Hyp J p f := by
  intro F _ _ _ _ h θ hθ A _ _ hA α _ hsq hE
  exact GenLocU3E8Frame.gammaAct_eq_top_of_exc7E8 h
    (GenLocU3Small.ne_two_of_pow h.one_le (Or.inr (Or.inl hq))) hq hθ hA α hsq hE

theorem genProp_psu3_seven {J : Type} [Group J] {p f : ℕ}
    (hq : p ^ f = 7) (hJ : LieModel J .PSU 3 p f) : GenProp J :=
  GenLocU3Seven.genProp_psu3_seven_of_exc8 hq hJ (exc7E8Hyp hq)

end CFSG.GH74.Generic.BProg.B2
