module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8AFrameBase
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8LiftFour
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8LiftInvsec

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Bender.Thm2

theorem aframe_thm : AFrameThm := by
  intro G _ _ z S ctx H _ hSH V hV hVO
  exact ⟨zbar H z (hSH ctx.z_mem), (aframe_easy ctx hSH hV hVO).toAFrame (aframe_invsec ctx H)
    (aframe_four_field ctx H) (aframe_cbar_field ctx H)⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
