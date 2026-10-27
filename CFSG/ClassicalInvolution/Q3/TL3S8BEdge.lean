module

public import CFSG.ClassicalInvolution.Q3.TL3S8BAssembly
public import CFSG.ClassicalInvolution.Q3.TL3Induct

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

section Edge


theorem tightLargeEdge_of_thm6SylowBelow {IH : ℕ → Prop} (hI : TightThm6SylowBelow IH) (n : ℕ)
    (hIH : CIT3Below n → TightBelow n → IH n) : TightLargeEdge n := by
  intro hA hb Y _ _ hn R S t hd hc hE2 hQ hlarge he
  have hF : TightFStarOK Y t := TightFStarOK.of_quasisimple hd.order hQ hc.2.2 hE2
  have d : OddByQuat R ((S : Subgroup R).map R.subtype) t :=
    OddByQuat.of_quaternion S hd.quat hd.mem hd.order hd.cent hd.normal hd.twoGroup
  obtain ⟨T, hT, -⟩ := exists_isSylow2Of_ge d.S_two
    (Subgroup.le_normalizer : ((S : Subgroup R).map R.subtype : Subgroup Y) ≤ _)
  by_cases hsyl : IsSylow2Of T ⊤
  · refine hlarge (hI Y ?_ R S t hd hF hc.1 T hT hsyl he)
    rw [hn]
    exact hIH hA hb
  · exact hd.not_dEdgeless_of_not_sylow hT hsyl he

end Edge

end CFSG.ClassicalInvolution.Q3
