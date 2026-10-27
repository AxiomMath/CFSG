module

public import CFSG.GH74.GLS.Stage2.Local.P34Sp4Max
public import CFSG.GH74.GLS.Stage2.Local.P34Sp4OddA
public import CFSG.GH74.GLS.Stage2.Local.P34Sp4OddM

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

theorem sp4OddCore : Sp4OddCore := by
  refine sp4OddCore_of_aut ?_
  intro F _ _ hodd β hβ h1 h2
  exact odd_aut_fix_trivial hodd hβ h1 h2

theorem sp4Facts : Sp4Facts := ⟨sp4Fusion, sp4Max, sp4OddCore⟩

end CFSG.GH74.GLS.Stage2.Local.P34
