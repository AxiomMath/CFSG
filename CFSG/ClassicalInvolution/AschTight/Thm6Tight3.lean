module

public import CFSG.ClassicalInvolution.AschTight.Thm6Tight2
public import CFSG.ClassicalInvolution.AschTight.Sec19Targets4

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable (p f : ℕ) [Fact p.Prime]

theorem tightControlledD_of_targets3 (hB3 : GoldschmidtB3Tmp) (hE2 : C19_E2Tmp p f)
    (h16 : C19_16STmp p f) (hIH : IHAllD p f) : TightControlledD p f := by
  intro G _ _ _ K z ht0
  have ht := S19R.tightStd_of_tightBranchD ht0
  by_cases hc : ConcOrTF4 G
  · exact hc.conclusionD ht.branch.notFourGenerated
  exfalso
  by_cases hA : AllTypeTwo K z
  · exact false_of_allTypeTwo hB3 ht hA
  obtain ⟨Q₀, S, hRS, -, hSz, -⟩ := exists_sylow_setup ht
  obtain ⟨W, hWmem, hWS⟩ := exists_wSet_le ht S
  have hd : Sec19Data p f K z S W :=
    ⟨ht, hA, hIH G K z ht.branch, hc, ⟨Q₀, hRS⟩, hSz, hWmem, hWS⟩
  have hE2' := cStarTwoRankOne_of_c19_E2Tmp hE2 hd
  have hE3 := normalizerQuotientTwoGeneratedStar_of_innerDiagonalTwo ht.branch.odd
    ht.branch.five ht.branch.member (innerDiagonalTwo_of_sec19 h16 hd)
  exact ht.branch.notFourGenerated (twoSubgroupsFourGenerated_of_edgeless_star ht.branch.odd
    ht.branch.five ht.branch.member ht0.control (deltaEdgeless_of_dEdgeless ht.edgeless)
    (commutingSylowForcesCommuting_of_tightD ht) hE2' hE3)

end CFSG.ClassicalInvolution.Disconnected.AschTight
