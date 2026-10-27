module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSection
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M11
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M12
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22Tight
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24Tight
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M23
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeWrap
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4OutFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42HSMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42RuMain
public import CFSG.Sporadic.Bridge.M11
public import CFSG.Sporadic.Bridge.M12
public import CFSG.Sporadic.Bridge.M22
public import CFSG.Sporadic.Bridge.J2
public import CFSG.Sporadic.Bridge.M23Surj
public import CFSG.Sporadic.Bridge.M24Surj
public import CFSG.Sporadic.Bridge.HSSurj
public import CFSG.Sporadic.Bridge.HeSurj
public import CFSG.Sporadic.Bridge.J4Surj
public import CFSG.Sporadic.Bridge.RuSurj
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFInputs

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

open CFSG.HardMathSupport.Cooperstein.Coordinator

theorem noIrrFFOffender_of_exclusion {s : TauCeti.SporadicName}
    (hex : CFSG.QuasithinUnique.Setup.X1.SporadicExclusion s)
    (hiso : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃*
      (TauCeti.CFSGIndex.sporadic s).Group)) :
    NoIrrFFOffender (TauCeti.CFSGIndex.sporadic s).Group := by
  intro W _ _ hW L E hq hirr hY hE hEne hEel hquad
  obtain ⟨e⟩ := hY
  obtain ⟨f⟩ := hiso
  exact hex W hW L E hq hirr ⟨e.trans f.symm⟩ hE hEne hEel hquad

theorem noIrrFFOffender_M11 :
    NoIrrFFOffender (TauCeti.CFSGIndex.sporadic .M11).Group :=
  noIrrFFOffender_of_exclusion (CFSG.QuasithinUnique.Setup.X1.sporadicExclusion_M11) (CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv)

theorem noIrrFFOffender_M12 :
    NoIrrFFOffender (TauCeti.CFSGIndex.sporadic .M12).Group :=
  noIrrFFOffender_of_exclusion (CFSG.QuasithinUnique.Setup.X1.sporadicExclusion_M12) (CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv)

theorem noIrrFFOffender_M22 :
    NoIrrFFOffender (TauCeti.CFSGIndex.sporadic .M22).Group :=
  noIrrFFOffender_of_exclusion (CFSG.QuasithinUnique.Setup.X1.sporadicExclusion_M22_of CFSG.QuasithinUnique.Setup.X1.m22TightProp) (CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv)

theorem noIrrFFOffender_M23 :
    NoIrrFFOffender (TauCeti.CFSGIndex.sporadic .M23).Group :=
  noIrrFFOffender_of_exclusion (CFSG.QuasithinUnique.Setup.X1.sporadicExclusion_M23) (CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv)

theorem noIrrFFOffender_M24 :
    NoIrrFFOffender (TauCeti.CFSGIndex.sporadic .M24).Group :=
  noIrrFFOffender_of_exclusion (CFSG.QuasithinUnique.Setup.X1.sporadicExclusion_M24_of CFSG.QuasithinUnique.Setup.X1.m24TightProp) (CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv)

theorem noIrrFFOffender_J1 :
    NoIrrFFOffender (TauCeti.CFSGIndex.sporadic .J1).Group :=
  noIrrFFOffender_of_exclusion (CFSG.QuasithinUnique.Setup.X1.sporadicExclusion_of_J1 CFSG.QuasithinUnique.Setup.X1.j1ExclusionProp) (CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv)

theorem noIrrFFOffender_J2 :
    NoIrrFFOffender (TauCeti.CFSGIndex.sporadic .J2).Group :=
  noIrrFFOffender_of_exclusion (CFSG.QuasithinUnique.Bridge.J2Excl.sporadicExclusion_J2) (CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv)

theorem noIrrFFOffender_J4 :
    NoIrrFFOffender (TauCeti.CFSGIndex.sporadic .J4).Group :=
  noIrrFFOffender_of_exclusion (CFSG.QuasithinUnique.Setup.X1.sporadicExclusion_J4_proved) (CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv)

theorem noIrrFFOffender_HS :
    NoIrrFFOffender (TauCeti.CFSGIndex.sporadic .HS).Group :=
  noIrrFFOffender_of_exclusion (CFSG.QuasithinUnique.Bridge.HSExcl.sporadicExclusion_HS) (CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv)

theorem noIrrFFOffender_He :
    NoIrrFFOffender (TauCeti.CFSGIndex.sporadic .He).Group :=
  noIrrFFOffender_of_exclusion (CFSG.QuasithinUnique.Setup.X1.sporadicExclusion_He) (CFSG.Sporadic.Bridge.He.nonempty_mulEquiv)

theorem noIrrFFOffender_Ru :
    NoIrrFFOffender (TauCeti.CFSGIndex.sporadic .Ru).Group :=
  noIrrFFOffender_of_exclusion (CFSG.QuasithinUnique.Bridge.RuExcl.sporadicExclusion_Ru) (CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv)

theorem noIrrFFOffender_sporadic (n : TauCeti.SporadicName)
    (hn : IsSQTKSporadic n) :
    NoIrrFFOffender (TauCeti.CFSGIndex.sporadic n).Group := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact noIrrFFOffender_M11
  · exact noIrrFFOffender_M12
  · exact noIrrFFOffender_M22
  · exact noIrrFFOffender_M23
  · exact noIrrFFOffender_M24
  · exact noIrrFFOffender_J1
  · exact noIrrFFOffender_J2
  · exact noIrrFFOffender_J4
  · exact noIrrFFOffender_HS
  · exact noIrrFFOffender_He
  · exact noIrrFFOffender_Ru

end CFSG.HardMathSupport.Cooperstein.Proving
