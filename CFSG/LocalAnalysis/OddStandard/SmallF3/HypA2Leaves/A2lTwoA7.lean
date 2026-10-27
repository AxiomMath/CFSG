module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LeavesV
public import CFSG.GH74.GLS.IVK.Lifted.TwoCoverRank

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup

theorem twoA7RankOne_holds : HypA2.TwoA7RankOne := by
  intro J _ _ hJ
  obtain ⟨hQ, hcard, he⟩ := hJ
  have hTwo : GH74.Uniqueness.SU.K.IsTwoAlt (J ⧸ CFSG.pPrimeCore 2 J) 7 :=
    ⟨hQ, inferInstance, hcard, he⟩
  obtain ⟨π, hπ⟩ := GH74.Uniqueness.SU.SU13.TA.TwoCover.exists_of_isTwoAlt hTwo
  have h1 := GH74.GLS.IVK.Lifted.pRank_eq_one_of_twoCover_seven hπ
  rw [← GH74.GLS.IVK.Lifted.pRank_two_quot_pPrimeCore J, h1]

end CFSG.OddStandard.SmallF3.HypA2Leaves
