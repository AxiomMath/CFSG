module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Close
public import Certificates.Certificate6134

public section

namespace CFSG.OddStandard.Seitz77

theorem caseBG0_false_of_certificate
    {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (h : Hyp G A) (d : Datum A) {G₁ G₂ S₀ W₁ W₂ : Subgroup G}
    (c : CaseBG0 d G₁ G₂ S₀ W₁ W₂) : False :=
  caseBG0_false Certificates.certificate6134 h d c

end CFSG.OddStandard.Seitz77
