module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Sp6B
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4O8D

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

theorem e4QuatGraphFacts_of_exLie
    {M : Type} [Group M]
    [Finite M] (hM : PhilipHall.QuaternionBridge.ExLie M) : E4QuatGraphFacts M :=
  hM.elim E4Sp6.e4QuatGraphFacts_PSp E4O8.e4QuatGraphFacts_POmegaPlus

theorem e4QuatNbrInv_of_exLie
    {M : Type} [Group M] [Finite M] (hM : PhilipHall.QuaternionBridge.ExLie M) :
    E4QuatNbrInv M :=
  hM.elim E4Sp6.e4QuatNbrInv_PSp E4O8.e4QuatNbrInv_POmegaPlus

theorem e4QuatActs3_of_exLie
    {M : Type} [Group M] [Finite M] (hM : PhilipHall.QuaternionBridge.ExLie M) :
    E4QuatActs3 M :=
  hM.elim E4Sp6.e4QuatActs3_PSp E4O8.e4QuatActs3_POmegaPlus

theorem secIdE4Edge_proved :
    SecIdE4Edge :=
  secIdE4Edge_of_graphFacts fun _ _ _ hM => e4QuatGraphFacts_of_exLie hM

theorem secIdE4DStar_proved :
    SecIdE4DStar :=
  secIdE4DStar_of_graphFacts fun _ _ _ hM => e4QuatGraphFacts_of_exLie hM

theorem secIdE4LinkCent_proved :
    SecIdE4LinkCent :=
  secIdE4LinkCent_of_nbrInv fun _ _ _ hM => e4QuatNbrInv_of_exLie hM

end CFSG.ClassicalInvolution.Q3.TL4
