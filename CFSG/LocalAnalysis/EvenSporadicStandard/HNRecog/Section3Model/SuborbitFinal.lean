module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.ElevenFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.SylowCentreFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TableIVFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TableVI5AFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TableVIFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TableXFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TwoFourFinal

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

@[expose] def Simple2S5 : Prop :=
  ∀ (H : Type) [Group H] (E : Subgroup H), TwoHS.IsF5Centralizer H E →
    ∀ S : Subgroup H, IsSimpleGroup ↥S → ∀ t : ↥S, t ^ 2 = 1 → t ≠ 1 →
      IsNonsplitDoubleCoverOfS5 ↥(Subgroup.centralizer ({t} : Set ↥S)) → IsShapeU35 ↥S

section Cert


theorem suborbitFacts_of_simple_2S5 (h : Simple2S5) : SuborbitFacts where
  sylow_centre := suborbitFacts_sylow_centre
  tableIV := suborbitFacts_tableIV
  tableVI := suborbitFacts_tableVI
  tableVI_5A_b := suborbitFacts_tableVI_5A_b
  two_four := suborbitFacts_two_four
  tableX := suborbitFacts_tableX
  simple_2S5 := h
  eleven_one_class := suborbitFacts_eleven_one_class

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section3
