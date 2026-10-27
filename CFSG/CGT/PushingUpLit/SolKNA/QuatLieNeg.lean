module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieNegPSL4
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieNegPSL5
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieNegPSU4
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieNegPSp4
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieNegTD4

public section

namespace CFSG.CGT.PushingUpLit.SolKNA


theorem neg3Table_holds : Neg3Table :=
  neg3Table_of_five negModel_PSL4 negModel_PSL5 negModel_PSU4 negModel_PSp4 negModel_TD4

end CFSG.CGT.PushingUpLit.SolKNA
