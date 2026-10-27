module

public import Certificates.Certificate3221

public section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

theorem p_list_facts : PListFacts :=
  Certificates.certificate3221.1

theorem pPlus_facts :
    SubListFacts pPlusGens pPlusIdx pPlusMask pPlusWords :=
  Certificates.certificate3221.2.1

theorem q1_facts : SubListFacts q1Gens q1Idx q1Mask q1Words :=
  Certificates.certificate3221.2.2.1

theorem q0_facts : SubListFacts q0Gens q0Idx q0Mask q0Words :=
  Certificates.certificate3221.2.2.2.1

theorem layer_list_facts : LayerFacts :=
  Certificates.certificate3221.2.2.2.2.1

theorem lift1_check : lift1Check = true :=
  Certificates.certificate3221.2.2.2.2.2.1

theorem lift0_check : lift0Check = true :=
  Certificates.certificate3221.2.2.2.2.2.2.1

theorem u_list_facts : UListFacts :=
  Certificates.certificate3221.2.2.2.2.2.2.2

end CFSG.EvenSmallLie.OmegaEight.Weyl
