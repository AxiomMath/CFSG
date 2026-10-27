module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf62E4Slot
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf62E4Sp6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf62E4O8

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace TwinDisc

theorem e4Sp6SqModel_of_certs :
    ExitE4.E4Sp6SqModel :=
  fun _ _ _ hM _ _ hq hinv htw _ hK' hne hle β h1 h2 =>
    ExitE4.sp62_aut_sq hM hq hinv htw hK' hne hle β h1 h2

theorem e4O8TwinModel_of_certs :
    ExitE4.E4O8TwinModel :=
  fun _ _ _ hM _ _ hq hinv htw => ExitE4.o82_two_twins hM hq hinv htw

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
