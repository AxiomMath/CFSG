module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434SporS1Base
public import CFSG.RankThree.PartOne.CTP.SporadicNoncomm
public import CFSG.RankThree.PartOne.KS.Co1ScalCheck

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434

open CFSG.Blueprint
open CFSG.RankThree.PartOne.StrongP (HasNoncommPair)

theorem HasNonabelianFiveSubgroup.of_noncommPair {G : Type*} [Group G] (h : HasNoncommPair 5 G) :
    HasNonabelianFiveSubgroup G := by
  obtain ⟨x, y, -, -, hxy, hP⟩ := h
  refine ⟨Subgroup.closure {x, y}, hP, fun hc => hxy ?_⟩
  exact congrArg Subtype.val
    (mul_comm' (⟨x, Subgroup.subset_closure (by simp)⟩ : Subgroup.closure ({x, y} : Set G))
      ⟨y, Subgroup.subset_closure (by simp)⟩)

theorem hs_hasNonabelianFiveSubgroup :
    HasNonabelianFiveSubgroup NativeSporadic.HS :=
  .of_noncommPair CFSG.RankThree.PartOne.CTP.hasNoncommPair_HS

theorem mcl_hasNonabelianFiveSubgroup :
    HasNonabelianFiveSubgroup NativeSporadic.McL :=
  .of_noncommPair CFSG.RankThree.PartOne.CTP.hasNoncommPair_McL

theorem ru_hasNonabelianFiveSubgroup :
    HasNonabelianFiveSubgroup NativeSporadic.Ru :=
  .of_noncommPair CFSG.RankThree.PartOne.CTP.hasNoncommPair_Ru

theorem co3_hasNonabelianFiveSubgroup :
    HasNonabelianFiveSubgroup NativeSporadic.Co3 :=
  .of_noncommPair CFSG.RankThree.PartOne.CTP.hasNoncommPair_Co3

theorem co2_hasNonabelianFiveSubgroup :
    HasNonabelianFiveSubgroup NativeSporadic.Co2 :=
  .of_noncommPair CFSG.RankThree.PartOne.CTP.hasNoncommPair_Co2

theorem th_hasNonabelianFiveSubgroup :
    HasNonabelianFiveSubgroup NativeSporadic.Th :=
  .of_noncommPair CFSG.RankThree.PartOne.CTP.hasNoncommPair_Th

theorem co1_hasNonabelianFiveSubgroup :
    HasNonabelianFiveSubgroup NativeSporadic.Co1 := by
  have hR := CFSG.RankThree.PartOne.KS.Co1Scal.co1Scal_rel
  have hC := hR.commData
  have hz := hC.orderOf_z
  refine hasNonabelianFiveSubgroup_of_heis
    (SporS1.heisRel_of_bcomm (hC.pow_q 0) (hC.pow_q 1) (hz ▸ pow_orderOf_eq_one _) (hC.comm_z 0)
      (hC.comm_z 1) hR.z_eq) ?_
  intro h1
  rw [h1, orderOf_one] at hz
  exact absurd hz (by norm_num)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434
