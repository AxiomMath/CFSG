module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
public import CFSG.Sporadic.Co2Schreier.Components
public import CFSG.Sporadic.Co2Schreier.FullAut

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert
open CFSG.ComponentClassification.OuterAutomorphisms

theorem sporadicCase_Co2 : SporadicCase .Co2 :=
  sporadicCase_of_comps
    (fun G _ _ ⟨e⟩ t ht B hB =>
      absurd hB (CTI_Co2_involution_centralizers_have_no_components e t ht B))
    (outer_of_forall_inner
      (mem_inner_of_mulEquiv co2PermEquiv CTUC_Co2_full_automorphisms_inner))

end CFSG.ComponentClassification.RestrictedStd.Spor
