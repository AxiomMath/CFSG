module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67FamSpor
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Red
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporM11
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporM12
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporM22
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporM23

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG CFSG.Blueprint

theorem cf67M11_thm :
    CF67M11 :=
  cf67Fam_of_noN2 fun Y _ _ h => noN2_M11 Y h

theorem cf67M12_thm :
    CF67M12 :=
  cf67Fam_of_noN2 fun Y _ _ h => noN2_M12 Y h

theorem cf67M22_thm :
    CF67M22 :=
  cf67Fam_of_noN2 fun Y _ _ h => noN2_M22 Y h

theorem cf67M23_thm :
    CF67M23 :=
  cf67Fam_of_noN2 fun Y _ _ h => noN2_M23 Y h

end CFSG.GH74.GLS.Stage2.Bender.Thm1
