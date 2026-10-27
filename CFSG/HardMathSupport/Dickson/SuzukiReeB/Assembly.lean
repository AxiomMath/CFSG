module

public import CFSG.HardMathSupport.Dickson.SuzukiReeB.Suzuki
public import CFSG.HardMathSupport.Dickson.SuzukiReeB.SmallRee
public import CFSG.HardMathSupport.Dickson.SuzukiReeB.LargeRee
public import CFSG.HardMathSupport.Dickson.SuzukiReeB.Tits
public import CFSG.Yardstones.Md42047359a2a.Definitions

public section

namespace CFSG.HardMathSupport.Dickson.SuzukiReeB


theorem lieSemisimpleCentSuzukiReeTits :
    CFSG.Yardstones.Md42047359a2a.LieSemisimpleCentSuzukiReeTits := by
  intro S _ _ hS hnc idx hfam he p hp hp2 hpc β hβ hβ1
  haveI := hS
  obtain ⟨d, hv⟩ := idx
  cases d with
  | suzuki m => exact perfectInLayer_suzuki m hv hnc he hp hp2 hβ hβ1
  | reeG2 m =>
    have hp3 : p ≠ 3 := by
      intro h3; apply hpc; rw [h3]; exact (TauCeti.LieTypeIndex.characteristic_reeG2 m).symm
    exact perfectInLayer_reeG2 m hv hnc he hp hp2 hp3 hβ hβ1
  | reeF4 m => exact perfectInLayer_reeF4 m hv hnc he hp hp2 hβ hβ1
  | tits => exact perfectInLayer_tits hv hnc he hp hp2 hβ hβ1
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hfam

end CFSG.HardMathSupport.Dickson.SuzukiReeB
