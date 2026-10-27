module

public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Stage2.Signalizer.L199PartII

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L199

theorem ig_19_9 : CFSG.GH74.GLS.Bg.B_signalizer_19_9 := by
  intro X _ _ z hz r hr hr2 R hR hinv hcomm
  have h : SigData X z r R := ⟨hz, hr, hr2, hR, hinv, hcomm⟩
  exact ⟨fun p hp hp2 hpr => part_one h hp hp2 hpr, fun hY => part_two h hY⟩

end CFSG.GH74.GLS.Stage2.Signalizer.L199
