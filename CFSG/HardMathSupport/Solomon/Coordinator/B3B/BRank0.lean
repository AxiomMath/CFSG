module

public import Certificates.Certificate36921
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Fuse
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocalCore

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.B3B

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.Sporadic.Bridge CFSG.Sporadic.Fi23
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

set_option linter.unusedSectionVars false


theorem rk_phiB_t3_zero : rk (phiB (t3 0)) = 2862 := by
  have e : phiB (t3 0) = Fi23InB.img 2 * Fi23InB.img 3 := by
    change phiB (Fi23.img 2 * Fi23.img 3) = _
    rw [map_mul, phiB_img (by norm_num), phiB_img (by norm_num)]
  unfold rk
  rw [e]
  exact Certificates.certificate36921 Fi23InB.gA Fi23InB.gB Fi23InB.φ_gA Fi23InB.φ_gB

section Classes


theorem isConj_phiB_t3_one_of_rk {s : NativeSporadic.B}
    (hs : orderOf s = 3) (hrk : rk s = 2916) : IsConj s (phiB (t3 1)) := by
  obtain ⟨i, hi⟩ := bThree_classes s hs
  have h0 : ¬ IsConj s (phiB (t3 0)) := fun hc => by
    have e := CFSG.Monster.Existence.rank_sub_one_of_isConj hc
    have h1 : rk s = rk (phiB (t3 0)) := e
    rw [hrk, rk_phiB_t3_zero] at h1
    omega
  fin_cases i
  · exact absurd hi h0
  · exact hi
  · exact absurd (hi.trans bThreeRc_holds) h0
  · exact hi.trans bThreeRd_holds

end Classes

end CFSG.HardMathSupport.Solomon.Coordinator.B3B
