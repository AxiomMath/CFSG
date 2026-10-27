module

public import CFSG.LocalAnalysis.OddStandard.Solomon75GH71
public import CFSG.Sporadic.Recognition.JankoWongMain
public import CFSG.LocalAnalysis.OddStandard.Solomon75Recognition

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

section Recognition

theorem solomon44McL_of_oddCore (hO : Solomon44OddCore 8) : Solomon44McL := by
  intro G _ _ hs hnonab t ht hcov
  have hbot := hO G hnonab t ht hcov
  have hC : IsDoubleCoverOfAlt ↥(centralizer ({t} : Set G)) 8 :=
    isDoubleCoverOfAlt_of_quot_bot hbot hcov
  obtain ⟨hq, hc, ⟨φ⟩⟩ := hC
  have htC : CFSG.Sporadic.Recognition.JankoWong.zIn t ∈ center ↥(centralizer ({t} : Set G)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_singleton_iff.1 y.2)
  have hZ : center ↥(centralizer ({t} : Set G)) =
      zpowers (CFSG.Sporadic.Recognition.JankoWong.zIn t) := by
    refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
    · exact zpowers_le.2 htC
    · rw [hc, Nat.card_zpowers]
      change 2 ≤ orderOf (⟨t, _⟩ : ↥(centralizer ({t} : Set G)))
      rw [Subgroup.orderOf_mk, ht]
  exact CFSG.Sporadic.Recognition.JankoWong.mclRecognition G hs hnonab t ht hq.1 hZ
    ⟨(QuotientGroup.quotientMulEquivOfEq hZ.symm).trans φ⟩

end Recognition

end CFSG.OddStandard.Solomon75
