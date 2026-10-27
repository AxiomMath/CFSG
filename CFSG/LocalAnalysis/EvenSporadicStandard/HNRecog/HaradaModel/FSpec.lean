module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.R0Spec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.NormSpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.HNRecog.HaradaLA

section Cert


theorem f_le_centralizer (hP : Nat.card ↥P1408 = 177408000) :
    wordSubgroupP fWords ≤ centralizer ({pZ₁} : Set ↥P1408) :=
  (r0Facts hP).f_le_centralizer

theorem f_iso (hP : Nat.card ↥P1408 = 177408000) :
    Nonempty (↥(wordSubgroupP fWords) ≃* alternatingGroup (Fin 5)) :=
  (r0Facts hP).f_iso

section Coordinates

variable (ι : Multiplicative V6 →* ↥P1408) (hι : ∀ v : V6, ι (Multiplicative.ofAdd v) = iotaFun v)

include hι

theorem f_le_normalizer (hP : Nat.card ↥P1408 = 177408000) :
    wordSubgroupP fWords ≤ normalizer (ι.range : Set ↥P1408) :=
  ((f_le_centralizer hP).trans (centralizer_pZ₁_le_normGens ι hι hP)).trans
    (wordSubgroupP_normGens_le_normalizer ι hι)

end Coordinates

end Cert

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
