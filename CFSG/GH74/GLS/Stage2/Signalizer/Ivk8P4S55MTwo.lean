module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55ML28
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55ML216
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55ML34
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MU34
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MSz8

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open CFSG.Blueprint CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem n1fam_two :
    N1Fam FTwo := by
  intro Y _ _ p b R₀ hF hN
  rcases hF with h | h | h | h | h
  · exact (noN1_L28 h hN).elim
  · exact (noN1_L216 h hN).elim
  · exact (noN1_L34 h hN).elim
  · exact (noN1_U34 h hN).elim
  · exact (noN1_Sz8 h hN).elim

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
