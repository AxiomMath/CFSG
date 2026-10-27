module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
import CFSG.LocalAnalysis.ComponentClassification.SolvablePrimeCoreLayerLift
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBSharedCore

public section

namespace CFSG.ComponentClassification.UnbalancedGS

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_gsFixedLayer_of_commute {J : Subgroup G} {z g : G}
    (hgJ : g ∈ normalizer (J : Set G)) (hgz : g * z = z * g) :
    g ∈ normalizer (gsFixedLayer J z : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (pLayer ↥(J ⊓ centralizer ({z} : Set G)) 2).Characteristic :=
    CatalogueBPrimeJoin.pLayer_characteristic
  exact normalizer_le_normalizer_map_of_characteristic
    (J ⊓ centralizer ({z} : Set G)) (pLayer ↥(J ⊓ centralizer ({z} : Set G)) 2)
    (inf_normalizer_le_normalizer_inf ⟨hgJ, le_normalizer (mem_centralizer_singleton_iff.mpr hgz)⟩)

theorem mem_normalizer_gsFixedLayer {M : Subgroup G} {e g : G}
    (hgM : g ∈ normalizer (M : Set G)) (hge : g ∈ centralizer ({e} : Set G)) :
    g ∈ normalizer (gsFixedLayer M e : Set G) :=
  mem_normalizer_gsFixedLayer_of_commute hgM (mem_centralizer_singleton_iff.mp hge)

end CFSG.ComponentClassification.UnbalancedGS
