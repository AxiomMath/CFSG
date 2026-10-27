module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerFactsMain
public import Certificates.Certificate36408
public import Certificates.Certificate36409

public section

namespace CFSG.OddStandard.AltStdSmall4.Tower

open Subgroup CFSG.SCATWreath

variable {G : Type} [Group G] [Finite G] {t : G}

theorem wrFalse_holds : WrFalse :=
  wrFalse_of_towerFacts Certificates.certificate36408

theorem slFalse_holds : SlFalse :=
  slFalse_of_towerFacts Certificates.certificate36409

end CFSG.OddStandard.AltStdSmall4.Tower
