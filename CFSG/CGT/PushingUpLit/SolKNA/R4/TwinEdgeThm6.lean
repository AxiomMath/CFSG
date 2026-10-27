module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.PMMain
public import CFSG.CGT.PushingUpLit.SolKNA.R4.Sylow
public import CFSG.CGT.PushingUpLit.SolKNA.R4.F1Main
public import CFSG.CGT.PushingUpLit.SolKNA.R4.EndCore
public import CFSG.ClassicalInvolution.AschTight.Thm6TightB3
public import CFSG.CGT.PushingUpLit.SolKNA.TightR4Reduce
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Generic

section Cit3

theorem tightLargeEdgeSR_of_thm6SylowBelowSRc {r : ℕ} {IH : ℕ → Prop}
    (hI : TightThm6SylowBelowSRc r IH) (n : ℕ) (hIH : CIT3Below n → TightBelowR r n → IH n) :
    TightLargeEdgeSR r n := by
  intro hA hb Y _ _ _ hn hnab R S t hd hc _ hlarge he
  have d : OddByQuat R ((S : Subgroup R).map R.subtype) t :=
    OddByQuat.of_quaternion S hd.quat hd.mem hd.order hd.cent hd.normal hd.twoGroup
  obtain ⟨T, hT, -⟩ := exists_isSylow2Of_ge d.S_two
    (Subgroup.le_normalizer : ((S : Subgroup R).map R.subtype : Subgroup Y) ≤ _)
  by_cases hsyl : IsSylow2Of T ⊤
  · refine hlarge (hI Y ?_ hnab R S t hd hc hc.1 T hT hsyl he)
    rw [hn]
    exact hIH hA hb
  · exact hd.not_dEdgeless_of_not_sylow hT hsyl he

section Count

theorem tightLargeEdgeSR_holds {r : ℕ} (hr : 4 ≤ r) (n : ℕ) : TightLargeEdgeSR r n :=
  tightLargeEdgeSR_of_thm6SylowBelowSRc
    (tightThm6SylowBelowSRc_of_parts
      CFSG.ClassicalInvolution.Disconnected.AschTight.goldschmidtB3Tmp_holds
      (sylowPartsR_holds r) (tightC19_11bSR_of_F1 (tightF1SR_holds hr))
      (tightCountRc_of_pm hr (tightPMR r (fun n => CIT3Below n ∧ TightBelowR r n))))
    n (fun hA hb => ⟨hA, hb⟩)

end Count

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4
