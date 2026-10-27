module

public import CFSG.CGT.Foote81L6.MainL6Of
public import CFSG.CGT.Foote81L6.Bridge.Main

public section

namespace CFSG.CGT.Foote81L6

theorem footeL6Bridge_holds : FooteL6Bridge :=
  fun _ _ _ S hS => Bridge.footeData_of_psl6Sylow S hS

end CFSG.CGT.Foote81L6
