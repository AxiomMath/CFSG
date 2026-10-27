module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MM11
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MM12
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MM22
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MM23
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MJ1
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MJ2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MJ3

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open CFSG.Blueprint CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem n1fam_spor :
    N1Fam FSpor := by
  intro Y _ _ p b R₀ hF hN
  rcases hF with h | h | h | h | h | h | h
  · exact Or.inr (n1_M11 h hN)
  · exact (noN1_M12 h hN).elim
  · exact (noN1_M22 h hN).elim
  · exact (noN1_M23 h hN).elim
  · exact (noN1_J1 h hN).elim
  · exact (noN1_J2 h hN).elim
  · exact (noN1_J3 h hN).elim

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
