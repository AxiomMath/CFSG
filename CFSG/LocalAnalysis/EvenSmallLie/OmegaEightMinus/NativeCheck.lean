
module

public import Certificates.Certificate3002

public section

namespace CFSG.EvenSmallLie.OmegaEightMinus

theorem ns_check : nsCheck = true :=
  Certificates.certificate3002.1

theorem omegaChain_check : omegaChainCheck = true :=
  Certificates.certificate3002.2.1

theorem autChain_check : autChainCheck = true :=
  Certificates.certificate3002.2.2.1

theorem sylowChain_check : sylowChainCheck = true :=
  Certificates.certificate3002.2.2.2.1

theorem structure_check : structureCheck = true :=
  Certificates.certificate3002.2.2.2.2.1

theorem stab_check : stabCheck = true :=
  Certificates.certificate3002.2.2.2.2.2.1

theorem tree_check : treeLitCheck = true :=
  Certificates.certificate3002.2.2.2.2.2.2.1

theorem sylowReps_check : sylowRepsLitCheck = true :=
  Certificates.certificate3002.2.2.2.2.2.2.2.1

theorem cent0_check : cent0Check = true :=
  Certificates.certificate3002.2.2.2.2.2.2.2.2.1

theorem sa_facts : SAFacts :=
  Certificates.certificate3002.2.2.2.2.2.2.2.2.2.1

theorem fg_check : fgCheck = true :=
  Certificates.certificate3002.2.2.2.2.2.2.2.2.2.2.1

theorem odd_check : oddCheck = true :=
  Certificates.certificate3002.2.2.2.2.2.2.2.2.2.2.2.1

theorem invs_check : invsCheck = true :=
  Certificates.certificate3002.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.EvenSmallLie.OmegaEightMinus
