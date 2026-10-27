module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CF67SL34
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CF67SU34
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Red

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem cf67Two_thm :
    CF67Two := by
  apply cf67Fam_of_noN2
  intro Y _ _ hF
  rcases hF with h | h | h | h | h
  · exact noN2_L28 Y h
  · exact noN2_L216 Y h
  · exact noN2_L34 Y h
  · exact noN2_U34 Y h
  · exact noN2_Sz8 Y h

end CFSG.GH74.GLS.Stage2.Bender.Thm1
