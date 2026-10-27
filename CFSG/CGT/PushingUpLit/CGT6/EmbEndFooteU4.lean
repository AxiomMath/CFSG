module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndFoote
public import CFSG.CGT.PushingUpLit.CGT6M.FiveInspU4

public section

namespace CFSG.CGT.PushingUpLit.CGT6

theorem footeInspU4_holds (hGA : CFSG.Open.GriessAllModelsStatement) : FooteInspU4 :=
  fun Q _ hQ => CGT6M.coverInv_psu4 hGA Q hQ

theorem end415_of_exc (hM2 : H1NaturalSL2) (hM4 : SchurMultL2Two)
    (hGA : CFSG.Open.GriessAllModelsStatement) (hFoote : EndFoote) (hExc : FooteInspExc) :
    End415 :=
  end415_of_inputs hM2 hM4 hGA hFoote (footeInspU4_holds hGA) hExc

end CFSG.CGT.PushingUpLit.CGT6
