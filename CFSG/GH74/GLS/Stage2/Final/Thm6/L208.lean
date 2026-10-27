module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2Main
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208SpMain
public import CFSG.GH74.GLS.Stage2.Final.Thm6.Lemmas1

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6

open CFSG.GH74.GLS.Stage12

theorem lemma20_8_thm : Lemma20_8 := by
  intro G _ _ z k S M h hMC hk
  rcases hk with rfl | hk
  · exact L208g2.lemma20_8_g2 h hMC
  · exact L208Sp.lemma20_8_sporadic h hMC hk

end CFSG.GH74.GLS.Stage2.Final.Thm6
