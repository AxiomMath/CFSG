module

public import CFSG.CGT.Foote81L6.TheoremOne
public import CFSG.CGT.Foote81L6.TStruct.TAction

public section

namespace CFSG.CGT.Foote81L6

theorem footeB₀Commutes_holds : FooteB₀Commutes :=
  fun _ _ _ _ _ D => D.B₀_comm_conj_t

end CFSG.CGT.Foote81L6
