module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.Parts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.TwoStep
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.AltTwo

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
open CFSG.ComponentClassification.SolMax.FiveCat

theorem catHaradaTwoAS_of_parts (hleaf : FivePumpLeaf) (h4 : CatCentFour)
    (hL216 : NoTwoCfgL216) (hL34 : NoTwoCfgL34) (hU34 : NoTwoCfgU34)
    (hL225 : NoTwoCfgL225) (hL35 : NoTwoCfgL35) (hU35 : NoTwoCfgU35)
    (hPSp : NoTwoCfgPSp45) (hJ1 : NoTwoCfgJ1) (hJ2 : NoTwoCfgJ2)
    (hM12 : NoTwoCfgM12) : CatHaradaTwoAS := by
  intro G _ _ S hSn hS hnab hcat hcent t v ht hv J hJ hdisj hcomm hC hCv hCtv
  have h : TwoCfg t v J := ⟨ht, hv, hJ, hdisj, hcomm, hC, hCv, hCtv⟩
  haveI := hSn
  rcases fivePumpOutcome_two hleaf h4 hSn hS hnab hcat hcent h with ⟨m, hm, hm7, ⟨θ⟩⟩ | hnon
  · exact alt_arm_two hSn hcent h hm hm7 θ (derived_le_of_two h4 hSn hS hnab hcat hcent h)
  · have hder := derived_le_of_two h4 hSn hS hnab hcat hcent h
    rcases hnon with h' | h' | h' | h' | h' | h' | h' | h' | h' | h'
    · exact hL216 G S hSn h' hcent t v J h hder
    · exact hL34 G S hSn h' hcent t v J h hder
    · exact hU34 G S hSn h' hcent t v J h hder
    · exact hL225 G S hSn h' hcent t v J h hder
    · exact hL35 G S hSn h' hcent t v J h hder
    · exact hU35 G S hSn h' hcent t v J h hder
    · exact hPSp G S hSn h' hcent t v J h hder
    · exact hJ1 G S hSn h' hcent t v J h hder
    · exact hJ2 G S hSn h' hcent t v J h hder
    · exact hM12 G S hSn h' hcent t v J h hder

end CFSG.EvenSporadicStandard.HSStd.InvCent
