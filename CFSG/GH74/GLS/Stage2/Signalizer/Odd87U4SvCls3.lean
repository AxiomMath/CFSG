module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls3Main
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls3Cent3

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem u4Cls3_thm : U4Cls3 := fun _ _ _ _ _ h =>
  ⟨fun hodd α hα W hW => u4_cls3_irred h hodd α hα W hW,
   fun hodd _ α hα x hxc => u4_cls3_cent h hodd α hα x hxc,
   fun hq α hα x hxr hc => u4_cls3_cent3 h hq α hα x hxr hc⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
